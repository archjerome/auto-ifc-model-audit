#!/usr/bin/env python3
"""
ifc_audit.py - openBIM / IFC model-package review tool.  (v4)

Every finding carries a stable rule id (F01, G05, X02 ...) so it can be cited
in an email, a BEP or a comment back from the design team; --rules prints the
table.

What a given project, client or authority asks for is not built in - this tool
is run on projects in several countries, and any one region's requirements
baked in here would be wrong for all the others.  --profile FILE.json states
them as project data: the schema and MVD to expect, the thresholds, the words
to grade in, and an external checklist mapped onto the rule ids.  The report
then names every item on that checklist no rule examined, because a check that
did not run must not read as a check that passed.

Checks a folder (or list) of .ifc files for:
  * Spatial structure: IfcProject at the apex with IfcSite, IfcBuilding,
    IfcBuildingStorey and IfcSpace each aggregated into the one above it;
    every element contained in a storey, counting the containment an
    assembly's parts inherit from the assembly; and whether the storeys of
    the package agree on name and level across the discipline models.
    Levels are read in the survey datum rather than in project coordinates,
    because a model that carries the survey offset in its IfcSite placement
    and one that carries it in IfcMapConversion are both correct and land on
    the same real-world level.
  * Export setup: the ViewDefinition (MVD) the authoring tool declared in the
    file header, checked against the schema actually written.  A Revit export
    left on 'IFC 2x3 Coordination View' while the schema target is IFC4 names
    an IFC2x3 MVD inside an IFC4 file; the receiving side then gets the
    guarantees of neither, and nothing in the model tree shows it.
  * Classification: whether every geometric element says what it is - an
    IfcClass that is not a generic proxy, and a PredefinedType that is neither
    NOTDEFINED nor pushed to USERDEFINED.  A specific PredefinedType on the
    element's type object counts, because the occurrence inherits it.  Type
    objects marked USERDEFINED with no ElementType are reported separately:
    that one breaks a schema rule rather than merely being vague.
  * Geolocation: schema, units, IfcSite RefLat/Long/Elev, IfcMapConversion +
    IfcProjectedCRS, and the model position in BOTH project-local and
    real-world (map E/N/H) coordinates.
  * Duplicate elements: duplicate GlobalIds (schema error) and geometric
    duplicates, graded by evidence.  Two elements are only ever called
    duplicates when they share the same IFC class AND the same type / family
    name.  Elements that merely overlap are reported separately as
    interferences, never as duplicates.
  * Floating elements: physical elements anomalously far from the model,
    found with a median + MAD fence rather than a percentile envelope that
    stray clusters can widen until they hide inside it.
  * Cross-file consistency: schema/unit mix, whether the models agree on the
    storeys they are built on, and - most importantly - whether they agree on
    their IfcMapConversion, which is what actually decides whether a
    federated package lines up.  An all-zero IfcMapConversion is
    called out as a placeholder rather than counted as agreement.

Geometry
--------
No third-party dependencies.  Element extents are approximated by an
axis-aligned bounding box built from the element's Body representation, with
full placement matrices (rotation included) resolved through
IfcLocalPlacement -> IfcMappedItem -> IfcRepresentationMap -> solid.  This
matters: Revit exports structural framing with the ObjectPlacement sitting at
the storey origin and the real position buried in the swept solid's Position,
so a placement-only reading makes every beam on a level look coincident.

Length units are taken from the IfcProject's own IfcUnitAssignment (SI or
IfcConversionBasedUnit, so foot/inch models work); map coordinates are kept in
the unit the IfcProjectedCRS declares.  Nothing assumes millimetres.

Assumes standard one-entity-per-line STEP encoding (Revit, ArchiCAD, Tekla,
Civil3D all export this way).

Usage:
  python ifc_audit.py                                    # audit the current folder
  python ifc_audit.py <folder-with-ifc-files>            # audit a package
  python ifc_audit.py model1.ifc model2.ifc ...          # audit specific files
  python ifc_audit.py <folder> --json report.json        # also dump raw JSON
  python ifc_audit.py <folder> --clash                   # add interference report
  python ifc_audit.py <folder> --float-k 4               # stricter float check
  python ifc_audit.py <folder> --float-z 20              # absolute float limit, m
  python ifc_audit.py <folder> --profile project.json   # project expectations
  python ifc_audit.py --rules                           # print the rule table
"""
import re, sys, os, json, math, glob, argparse, datetime, time
from collections import Counter, defaultdict

# ----------------------------------------------------------------------------
# STEP record parsing
# ----------------------------------------------------------------------------

RE_REC = re.compile(r"^#(\d+)\s*=\s*([A-Z0-9_]+)\s*\(")
RE_TUPLES = re.compile(r"\(([^()]*)\)")
# A rooted entity opens with a 22-char base64 GlobalId followed by OwnerHistory.
RE_GUID = re.compile(r"\('([0-9A-Za-z_$]{22})',(?:#\d+|\$),")

# Entities that are NOT IfcRoot subtypes but also start with a string attribute,
# so they can imitate the GlobalId pattern.  IfcPropertySingleValue('Reference',$,..)
# is the common offender: 22 legal characters followed by an absent second argument.
NON_ROOTED = ('IFCPROPERTY', 'IFCQUANTITY', 'IFCPHYSICAL', 'IFCMATERIAL',
              'IFCCLASSIFICATION', 'IFCLIBRARY', 'IFCDOCUMENT', 'IFCEXTERNAL',
              'IFCORGANIZATION', 'IFCPERSON', 'IFCAPPLICATION', 'IFCPOSTALADDRESS',
              'IFCTELECOMADDRESS', 'IFCPROFILEDEF', 'IFCPRESENTATION',
              'IFCSURFACESTYLE', 'IFCCURVESTYLE', 'IFCTEXTSTYLE', 'IFCFILLAREASTYLE')
ROOTED_ANYWAY = {'IFCPROPERTYSET', 'IFCPROPERTYSETTEMPLATE'}


def is_rooted(typ):
    return typ in ROOTED_ANYWAY or not typ.startswith(NON_ROOTED)


def parse_record(line):
    """Return (id, TYPE, argstring) for a STEP record line, else None."""
    m = RE_REC.match(line)
    if not m:
        return None
    body = line[m.end():]
    e = body.rfind(')')
    if e < 0:
        return None
    return int(m.group(1)), m.group(2), body[:e]


def split_args(s):
    """Split a STEP argument list on top-level commas, respecting quotes/parens."""
    out = []
    buf = []
    depth = 0
    instr = False
    i = 0
    n = len(s)
    while i < n:
        c = s[i]
        if instr:
            if c == "'":
                if i + 1 < n and s[i + 1] == "'":
                    buf.append("''")
                    i += 2
                    continue
                instr = False
            buf.append(c)
        elif c == "'":
            instr = True
            buf.append(c)
        elif c == '(':
            depth += 1
            buf.append(c)
        elif c == ')':
            depth -= 1
            buf.append(c)
        elif c == ',' and depth == 0:
            out.append(''.join(buf))
            buf = []
        else:
            buf.append(c)
        i += 1
    out.append(''.join(buf))
    return out


def arg(a, i):
    return a[i].strip() if i < len(a) else '$'


def ref(v):
    v = v.strip()
    return int(v[1:]) if v.startswith('#') else None


def reflist(v):
    return [int(x) for x in re.findall(r'#(\d+)', v)]


def num(v):
    try:
        return float(v.strip())
    except ValueError:
        return None


def sval(v):
    v = v.strip()
    return v[1:-1].replace("''", "'") if len(v) >= 2 and v[0] == "'" else None


def numtuple(v):
    v = v.strip()
    if not v.startswith('('):
        return None
    try:
        return tuple(float(x) for x in v[1:-1].split(',') if x.strip())
    except ValueError:
        return None


def point_rows(v):
    """'((1.,2.),(3.,4.))' -> [(1.0,2.0), (3.0,4.0)] for IfcCartesianPointList."""
    rows = []
    for g in RE_TUPLES.findall(v):
        try:
            rows.append(tuple(float(x) for x in g.split(',') if x.strip()))
        except ValueError:
            pass
    return rows


# ----------------------------------------------------------------------------
# Model view definition (MVD) and element classification
# ----------------------------------------------------------------------------

RE_VIEWDEF = re.compile(r"ViewDefinition\s*\[([^\]]*)\]", re.I)
RE_EXCHANGE = re.compile(r"ExchangeRequirement\s*\[([^\]]*)\]", re.I)
RE_COORDREF = re.compile(r"CoordinateReference\s*\[([^\]]*)\]", re.I)
RE_VIEW_VER = re.compile(r"^(.*?)[_\s]*V(\d[\d.]*)$", re.I)
RE_ENUM = re.compile(r"^\.([A-Z][A-Z0-9_]*)\.$")


def schema_family(schema):
    """'IFC4X3_ADD2' -> 'IFC4X3'.  The addendum never changes which MVD applies."""
    s = (schema or '?').upper().replace(' ', '')
    for fam in ('IFC4X3', 'IFC4X2', 'IFC4X1', 'IFC4', 'IFC2X3', 'IFC2X2'):
        if s.startswith(fam):
            return fam
    return s


# Base ViewDefinition name -> (schema families it belongs to, plain-English name)
MVD_SCHEMAS = {
    'COORDINATIONVIEW':            (('IFC2X3',), 'Coordination View'),
    'IFC2X3COORDINATIONVIEW':      (('IFC2X3',), 'Coordination View'),
    'SPACEBOUNDARYADDONVIEW':      (('IFC2X3',), 'Space Boundary Add-on View'),
    'QUANTITYTAKEOFFADDONVIEW':    (('IFC2X3',), 'Quantity Take-off Add-on View'),
    'FMHANDOVERVIEW':              (('IFC2X3',), 'FM Handover View'),
    'BASICFMHANDOVERVIEW':         (('IFC2X3',), 'Basic FM Handover View'),
    'COBIE2.4DESIGNDELIVERABLE':   (('IFC2X3',), 'COBie 2.4 Design Deliverable'),
    'STRUCTURALANALYSISVIEW':      (('IFC2X3', 'IFC4'), 'Structural Analysis View'),
    'REFERENCEVIEW':               (('IFC4', 'IFC4X1', 'IFC4X2', 'IFC4X3'),
                                    'Reference View'),
    'DESIGNTRANSFERVIEW':          (('IFC4', 'IFC4X1', 'IFC4X2', 'IFC4X3'),
                                    'Design Transfer View'),
    'ALIGNMENTBASEDREFERENCEVIEW': (('IFC4X1', 'IFC4X3'),
                                    'Alignment-based Reference View'),
}

# Views that restrict geometry to what a receiver only has to draw
LIGHTWEIGHT_VIEWS = {'REFERENCEVIEW', 'ALIGNMENTBASEDREFERENCEVIEW'}

# ViewDefinition strings a given exporter writes by schema rather than by the
# view setup chosen, so they carry no information about the MVD.  Revit writes
# 'CoordinationView' into every IFC4/IFC4x3 file and 'CoordinationView_V2.0'
# into every IFC2x3 file, whichever Reference View or Design Transfer View
# setup produced it.  Reporting that per model is N identical findings the
# author cannot act on; it is a fact about the tool, not about the model.
EXPORTER_ARTEFACTS = (
    ('REVIT', ('IFC4', 'IFC4X1', 'IFC4X2', 'IFC4X3'), 'COORDINATIONVIEW'),
)


def exporter_artefact(base, fam, tool):
    t = (tool or '').upper()
    return any(name in t and fam in fams and base == view
               for name, fams, view in EXPORTER_ARTEFACTS)


def split_view(v):
    """'ReferenceView_V1.2' -> ('REFERENCEVIEW', '1.2')."""
    s = (v or '').strip().replace(' ', '')
    m = RE_VIEW_VER.match(s)
    if m:
        return m.group(1).upper().rstrip('_'), m.group(2)
    return s.upper(), None


def view_status(view, schema, tool=None):
    """Grade the header ViewDefinition, then hold it to the schema it rides on.

    A correct MVD declaration on a superseded schema is still a model the rest
    of the package has to work around, so it never returns PASS - see
    _view_status for the MVD grading itself.
    """
    sev, text = _view_status(view, schema, tool)
    if sev == PASS and schema_family(schema) in NO_MAPCONV_SCHEMAS:
        return REVIEW, ('%s - but %s is itself superseded: no IfcMapConversion, '
                        'no PredefinedType on many classes, and generic flow '
                        'classes in place of real ones' % (text, schema))
    return sev, text


def _view_status(view, schema, tool=None):
    """Grade the header ViewDefinition against the schema actually written.

    A mismatch is worth reporting because anything that reads the header is
    told the wrong MVD.  It is NOT evidence that the wrong export setup was
    used: Revit's IFC4/IFC4x3 exporter has been observed writing
    'CoordinationView' into a file whose schema and ExchangeRequirement both
    match the IFC4x3 Reference View setup that was actually selected.  So the
    finding names the header as the unreliable part and says what to check,
    rather than sending the author back to re-export something they already
    exported correctly.
    """
    fam = schema_family(schema)
    if not view:
        return REVIEW, ('no ViewDefinition in the file header - nothing states '
                        'which MVD the export claims to follow')
    base, ver = split_view(view)
    known = MVD_SCHEMAS.get(base)
    if known is None:
        return REVIEW, 'ViewDefinition "%s" is not a recognised MVD name' % view
    fams, nice = known
    shown = nice + (' %s' % ver if ver else '')
    if fam not in fams:
        if exporter_artefact(base, fam, tool):
            return PASS, ('Revit writes "%s" for every %s export, including '
                          'the %s Reference View setup - the header records the '
                          'schema, not the MVD' % (view, fam, fam))
        return REVIEW, ('ViewDefinition "%s" is the %s MVD but the file is '
                        'written as %s, so anything reading the header is told '
                        'the wrong MVD; check the export setup against the '
                        'schema target' % (view, '/'.join(fams), schema))
    if base in LIGHTWEIGHT_VIEWS:
        return REVIEW, ('%s is a reference-only view - tessellation and swept '
                        'solids are in scope, Boolean/CSG and NURBS are not, so '
                        'it coordinates but will not carry editable geometry '
                        'downstream' % shown)
    return PASS, '%s, consistent with %s' % (shown, schema)


# IfcMapConversion and IfcProjectedCRS were introduced in IFC4.  A model on an
# older schema cannot carry either, so it can never reach LoGeoRef 50 and must
# be told to change schema rather than to fill in a MapConversion it has no
# place to put.
NO_MAPCONV_SCHEMAS = ('IFC2X3', 'IFC2X2')


def can_map_convert(schema):
    """False when the schema predates IfcMapConversion."""
    return schema_family(schema) not in NO_MAPCONV_SCHEMAS


def enum_val(s):
    """'.RIGIDSEGMENT.' -> 'RIGIDSEGMENT';  anything else -> None."""
    m = RE_ENUM.match(s.strip())
    return m.group(1) if m else None


def specific(v):
    """True when a PredefinedType actually says what the element is."""
    return v is not None and v not in ('NOTDEFINED', 'USERDEFINED')


# PredefinedType attribute index.  Almost every physical element carries it at
# position 8 - GlobalId, OwnerHistory, Name, Description, ObjectType,
# ObjectPlacement, Representation, Tag, PredefinedType.  These do not, and
# reading position 8 on them would report a neighbouring enum as the class:
# IfcDoor would answer with its OperationType.
PDT_DEFAULT = 8
PDT_INDEX = {
    'IFCDOOR': 10, 'IFCDOORSTANDARDCASE': 10,
    'IFCWINDOW': 10, 'IFCWINDOWSTANDARDCASE': 10,
    'IFCSTAIRFLIGHT': 12,          # NumberOfRisers, NumberOfTreads, RiserHeight, TreadLength
    'IFCREINFORCINGBAR': 12,       # SteelGrade, NominalDiameter, CrossSectionArea, BarLength
    'IFCREINFORCINGMESH': 17,
    'IFCDISTRIBUTIONSYSTEM': 6, 'IFCBUILDINGSYSTEM': 5, 'IFCBUILTSYSTEM': 5,
    # These sit at the default 8, and are pinned so the scan below can never
    # reach the enum that follows: IfcPile.ConstructionType,
    # IfcDistributionPort.FlowDirection, IfcTransportElement.OperationType.
    'IFCPILE': 8, 'IFCDISTRIBUTIONPORT': 8, 'IFCTRANSPORTELEMENT': 8,
}

# Type objects are uniform: ..., Tag, ElementType, PredefinedType
TYPE_ELEMTYPE_INDEX = 8
TYPE_PDT_INDEX = 9

# IFC2x3 gave these classes no PredefinedType at all, so a blank one is the
# schema's doing rather than the modeller's.  IfcBuildingElementProxy is here
# because IFC2x3 puts CompositionType in that slot - reading it as a
# PredefinedType would report every proxy as ELEMENT and call it classified.
NO_PDT_IFC2X3 = {
    'IFCWALL', 'IFCWALLSTANDARDCASE', 'IFCBEAM', 'IFCCOLUMN', 'IFCMEMBER',
    'IFCPLATE', 'IFCBUILDINGELEMENTPROXY', 'IFCDISCRETEACCESSORY',
    'IFCFASTENER', 'IFCMECHANICALFASTENER', 'IFCBUILDINGELEMENTPART',
    'IFCFURNISHINGELEMENT', 'IFCFLOWSEGMENT', 'IFCFLOWFITTING',
    'IFCFLOWTERMINAL', 'IFCFLOWCONTROLLER', 'IFCENERGYCONVERSIONDEVICE',
}

# Outright proxies: the exporter could not map the element to any IFC class
# and said so, whatever the PredefinedType then claims.
PROXY_CLASSES = {
    'IFCBUILDINGELEMENTPROXY', 'IFCBUILTELEMENT', 'IFCPROXY', 'IFCELEMENT',
    'IFCDISTRIBUTIONELEMENT',
}

# Generic supertypes.  Less damning than a proxy - an IFC2x3 MEP export often
# wrote IfcFlowSegment where IFC4 would write IfcPipeSegment - but still one
# level short of saying what the element is.
GENERIC_CLASSES = {
    'IFCDISTRIBUTIONFLOWELEMENT', 'IFCELEMENTCOMPONENT', 'IFCFLOWSEGMENT',
    'IFCFLOWFITTING', 'IFCFLOWTERMINAL', 'IFCFLOWCONTROLLER',
    'IFCFLOWMOVINGDEVICE', 'IFCFLOWSTORAGEDEVICE', 'IFCFLOWTREATMENTDEVICE',
    'IFCENERGYCONVERSIONDEVICE', 'IFCFURNISHINGELEMENT',
}

# Logical groupings that carry no geometry and are not classified as elements
NON_PHYSICAL = {
    'IFCDISTRIBUTIONSYSTEM', 'IFCBUILDINGSYSTEM', 'IFCBUILTSYSTEM', 'IFCSYSTEM',
    'IFCGROUP', 'IFCASSET', 'IFCINVENTORY', 'IFCELECTRICALCIRCUIT',
    'IFCSTRUCTURALANALYSISMODEL',
}


def elem_pdt(cls, args, fam):
    """PredefinedType of an occurrence -> (value, how).

    'how' is 'index' when the class's own attribute position was used, 'scan'
    when the layout was unknown and it had to be found by shape, and 'n/a' when
    the class has no PredefinedType in this schema at all.  Keeping 'how' is
    what stops an unknown class from being reported as confidently as a known
    one.
    """
    if fam == 'IFC2X3' and cls in NO_PDT_IFC2X3:
        return None, 'n/a'
    pinned = cls in PDT_INDEX
    i = PDT_INDEX.get(cls, PDT_DEFAULT)
    v = enum_val(arg(args, i))
    if v is not None:
        return v, 'index'
    if pinned:
        # The layout is known, so an empty slot really is empty.  Scanning on
        # would report the neighbouring enum - IfcDoor's OperationType,
        # IfcDistributionPort's FlowDirection - as the PredefinedType.
        return None, 'index'
    # Unknown layout.  IfcStairFlight and its like carry extra attributes ahead
    # of PredefinedType, leaving position 8 blank and the enum further along, so
    # a blank slot is not yet evidence that the element was left unclassified.
    for j in range(len(args) - 1, i, -1):
        v = enum_val(arg(args, j))
        if v is not None:
            return v, 'scan'
    return None, 'index' if arg(args, i) == '$' else 'scan'


def classify_elements(model, elems):
    """Grade every geometric element on IfcClass and PredefinedType.

    An element is only usable downstream if it says what it is, and two things
    break that without looking wrong in any viewer: an exporter that could not
    map the element to a real IFC class and fell back to a generic proxy, and a
    PredefinedType left NOTDEFINED or pushed to USERDEFINED.  A specific
    PredefinedType on the element's type object counts, because the occurrence
    inherits it, so both are read before anything is flagged.
    """
    rows = []
    counts = Counter()
    matrix = Counter()
    n = 0
    for e in elems:
        if e.ifc_class in NON_PHYSICAL:
            continue
        n += 1
        tpdt, telem, tname = model.type_info(e.id)
        eff, inherited = e.predefined, False
        if not specific(eff) and specific(tpdt):
            eff, inherited = tpdt, True
        named = e.object_type or telem or ''

        if e.ifc_class in PROXY_CLASSES:
            grade = FIX
            why = 'exported as a generic proxy, so the model never says what it is'
            act = ('map the family to a real IFC class in the Revit export - '
                   'IFC Export Classes, or an IfcExportAs type parameter')
        elif e.ifc_class in GENERIC_CLASSES:
            grade = REVIEW
            why = ('%s is the supertype, one level short of a class that says '
                   'what this is' % ifc_name(e.ifc_class))
            act = 'map the family to the specific IFC class in the Revit export'
        elif e.pdt_source == 'n/a':
            grade = PASS
            why = 'no PredefinedType on this class in %s' % model.schema
            act = ''
        elif specific(eff):
            grade = PASS
            why = eff + (' (inherited from the type)' if inherited else '')
            act = ''
        elif 'USERDEFINED' in (e.predefined, tpdt):
            if not named:
                grade = REVIEW
                why = ('USERDEFINED with no ObjectType or ElementType, so '
                       'nothing states what this element is')
                act = 'assign a proper PredefinedType, or name the type in ObjectType'
            else:
                grade = REVIEW
                why = 'USERDEFINED, described only as "%s"' % named
                act = 'set the matching %s PredefinedType' % ifc_name(e.ifc_class)
        elif 'NOTDEFINED' in (e.predefined, tpdt):
            grade = REVIEW
            why = ('NOTDEFINED on the element and its type'
                   if tpdt == 'NOTDEFINED' else
                   'NOTDEFINED, with no type to inherit one from')
            act = 'set a PredefinedType on the Revit type'
        else:
            grade = FIX
            why = 'PredefinedType not written at all'
            act = 'set a PredefinedType on the Revit type'

        counts[grade] += 1
        matrix[(e.ifc_class, e.predefined or '(absent)', grade)] += 1
        if grade != PASS or e.pdt_source == 'scan':
            rows.append({'id': e.id, 'class': e.ifc_class,
                         'predefined': e.predefined, 'type_predefined': tpdt,
                         'object_type': e.object_type, 'type_name': tname or '',
                         'grade': grade, 'why': why, 'action': act,
                         'read_by': e.pdt_source})

    rows.sort(key=lambda r: ({FIX: 0, REVIEW: 1, PASS: 2}[r['grade']], r['id']))
    return {
        'n': n,
        'n_classified': counts[PASS],
        'n_fix': counts[FIX],
        'n_review': counts[REVIEW],
        'n_proxy': sum(v for k, v in matrix.items() if k[0] in PROXY_CLASSES),
        'n_generic': sum(v for k, v in matrix.items() if k[0] in GENERIC_CLASSES),
        'n_scanned': sum(1 for r in rows if r['read_by'] == 'scan'),
        'matrix': sorted(((k[0], k[1], k[2], v) for k, v in matrix.items()),
                         key=lambda x: (x[0], -x[3])),
        'rows': rows[:5000],
        'n_rows': len(rows),
    }


def audit_type_objects(model):
    """An IfcTypeObject with PredefinedType USERDEFINED but no ElementType.

    Revit writes USERDEFINED whenever the family has no IFC equivalent, and
    leaves ElementType empty.  USERDEFINED itself is legitimate - it is the
    escape hatch the schema provides - but with ElementType blank the pair says
    nothing at all about what the type is, which is what makes it worth review
    rather than a silent pass.
    """
    bad = []
    for tid in model.type_ids:
        t, a = model.ent[tid]
        if enum_val(arg(a, TYPE_PDT_INDEX)) != 'USERDEFINED':
            continue
        if sval(arg(a, TYPE_ELEMTYPE_INDEX)):
            continue
        bad.append({'id': tid, 'class': t, 'name': sval(arg(a, 2)) or ''})
    return bad


# ----------------------------------------------------------------------------
# 3x4 transforms, stored as (R, t) with R row-major 9-tuple
# ----------------------------------------------------------------------------

IDENT = ((1., 0., 0., 0., 1., 0., 0., 0., 1.), (0., 0., 0.))


def mmul(A, B):
    """A applied after B."""
    Ra, ta = A
    Rb, tb = B
    R = tuple(Ra[i * 3] * Rb[j] + Ra[i * 3 + 1] * Rb[3 + j] + Ra[i * 3 + 2] * Rb[6 + j]
              for i in range(3) for j in range(3))
    t = tuple(Ra[i * 3] * tb[0] + Ra[i * 3 + 1] * tb[1] + Ra[i * 3 + 2] * tb[2] + ta[i]
              for i in range(3))
    return (R, t)


def mapply(A, p):
    R, t = A
    x = p[0]
    y = p[1]
    z = p[2] if len(p) > 2 else 0.
    return (R[0] * x + R[1] * y + R[2] * z + t[0],
            R[3] * x + R[4] * y + R[5] * z + t[1],
            R[6] * x + R[7] * y + R[8] * z + t[2])


def _norm(v):
    if not v:
        return None
    n = math.sqrt(sum(c * c for c in v))
    return tuple(c / n for c in v) if n > 1e-12 else None


def _cross(a, b):
    return (a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])


def _v3(v):
    if v is None:
        return None
    return (v[0], v[1], v[2] if len(v) > 2 else 0.)


def frame(origin, zdir, xdir):
    """Build (R,t) from an origin plus optional Z (axis) and X (ref direction)."""
    z = _norm(_v3(zdir)) or (0., 0., 1.)
    x = _norm(_v3(xdir))
    if x is None:
        x = (1., 0., 0.) if abs(z[0]) < 0.9 else (0., 1., 0.)
    d = x[0] * z[0] + x[1] * z[1] + x[2] * z[2]
    x = _norm((x[0] - d * z[0], x[1] - d * z[1], x[2] - d * z[2])) or (1., 0., 0.)
    y = _cross(z, x)
    R = (x[0], y[0], z[0], x[1], y[1], z[1], x[2], y[2], z[2])
    o = _v3(origin) or (0., 0., 0.)
    return (R, o)


# ----------------------------------------------------------------------------
# Axis-aligned bounding boxes: (xmin, ymin, zmin, xmax, ymax, zmax)
# ----------------------------------------------------------------------------

def bb_points(pts):
    x0 = y0 = z0 = float('inf')
    x1 = y1 = z1 = float('-inf')
    n = 0
    for p in pts:
        z = p[2] if len(p) > 2 else 0.
        if p[0] < x0: x0 = p[0]
        if p[0] > x1: x1 = p[0]
        if p[1] < y0: y0 = p[1]
        if p[1] > y1: y1 = p[1]
        if z < z0: z0 = z
        if z > z1: z1 = z
        n += 1
    return (x0, y0, z0, x1, y1, z1) if n else None


def bb_union(a, b):
    if a is None: return b
    if b is None: return a
    return (min(a[0], b[0]), min(a[1], b[1]), min(a[2], b[2]),
            max(a[3], b[3]), max(a[4], b[4]), max(a[5], b[5]))


def bb_transform(b, M):
    """AABB of the transformed box (exact when the local box is box-shaped)."""
    if b is None or M is IDENT:
        return b
    corners = ((b[0], b[1], b[2]), (b[0], b[1], b[5]), (b[0], b[4], b[2]),
               (b[0], b[4], b[5]), (b[3], b[1], b[2]), (b[3], b[1], b[5]),
               (b[3], b[4], b[2]), (b[3], b[4], b[5]))
    return bb_points(mapply(M, c) for c in corners)


def bb_vol(b):
    return max(0., b[3] - b[0]) * max(0., b[4] - b[1]) * max(0., b[5] - b[2])


def bb_inter_vol(a, b):
    dx = min(a[3], b[3]) - max(a[0], b[0])
    dy = min(a[4], b[4]) - max(a[1], b[1])
    dz = min(a[5], b[5]) - max(a[2], b[2])
    return dx * dy * dz if dx > 0 and dy > 0 and dz > 0 else 0.


def _padded(b, pad):
    return (b[0], b[1], b[2],
            max(b[3], b[0] + pad), max(b[4], b[1] + pad), max(b[5], b[2] + pad))


def bb_iou(a, b, pad=1.0):
    """Intersection-over-union; flat/linear boxes are padded so they stay comparable."""
    A = _padded(a, pad)
    B = _padded(b, pad)
    inter = bb_inter_vol(A, B)
    union = bb_vol(A) + bb_vol(B) - inter
    return inter / union if union > 0 else 0.


def bb_centre(b):
    return ((b[0] + b[3]) / 2, (b[1] + b[4]) / 2, (b[2] + b[5]) / 2)


def bb_diag(b):
    return math.sqrt((b[3] - b[0]) ** 2 + (b[4] - b[1]) ** 2 + (b[5] - b[2]) ** 2)


# ----------------------------------------------------------------------------
# Constants
# ----------------------------------------------------------------------------

SI_PREFIX = {'EXA': 1e18, 'PETA': 1e15, 'TERA': 1e12, 'GIGA': 1e9, 'MEGA': 1e6,
             'KILO': 1e3, 'HECTO': 1e2, 'DECA': 1e1, 'DECI': 1e-1, 'CENTI': 1e-2,
             'MILLI': 1e-3, 'MICRO': 1e-6, 'NANO': 1e-9, 'PICO': 1e-12}

# Spatial / logical / non-physical types excluded from element checks
EXCLUDE = {'IFCSITE', 'IFCBUILDING', 'IFCBUILDINGSTOREY', 'IFCSPACE', 'IFCSPATIALZONE',
           'IFCZONE', 'IFCGRID', 'IFCOPENINGELEMENT', 'IFCANNOTATION', 'IFCPROJECT',
           'IFCPROPERTYSET', 'IFCELEMENTQUANTITY', 'IFCMATERIALLAYERSET',
           'IFCMATERIALLAYERSETUSAGE', 'IFCPRESENTATIONLAYERASSIGNMENT',
           'IFCDISTRIBUTIONPORT', 'IFCVIRTUALELEMENT'}

# Representation identifiers that are not the solid body of the element
NON_BODY = {'Axis', 'FootPrint', 'Profile', 'SurveyPoints', 'Lighting', 'Box', 'Annotation'}

# The IFC4x3 spatial containers that take the place of IfcBuilding on
# infrastructure.  Before IFC4x3 none of these exist; from IFC4x3 an element
# can be contained in one, and a tool that did not read them would report
# every element of a bridge model as loose in the file.
FACILITY_TYPES = ('IFCFACILITY', 'IFCFACILITYPART', 'IFCBRIDGE', 'IFCROAD',
                  'IFCRAILWAY', 'IFCMARINEFACILITY')

# The spatial containers, read in their own pass.  IfcSite is handled beside
# the georeferencing it carries; the rest are read only as structure.
SPATIAL_TYPES = set(('IFCBUILDING', 'IFCBUILDINGSTOREY', 'IFCSPACE',
                     'IFCSPATIALZONE', 'IFCEXTERNALSPATIALELEMENT')
                    + FACILITY_TYPES)

# What each spatial class may hang from.  Wider than the textbook chain on
# purpose, because the alternatives are all legal and a false finding here
# would send someone to rebuild a correct model:
#
#   a site under a site        a campus split into plots
#   a building under a building  a complex aggregating its blocks
#   a storey under a storey    CompositionType PARTIAL, a split level
#   a building under a project IfcSite is optional in IFC4
#   a space under a building, a site or a facility   a plant yard or an
#                              external area has no storey to sit on
SPATIAL_PARENT = {
    'IFCSITE': ('IFCPROJECT', 'IFCSITE'),
    'IFCBUILDING': ('IFCSITE', 'IFCBUILDING', 'IFCPROJECT') + FACILITY_TYPES,
    'IFCBUILDINGSTOREY': ('IFCBUILDING', 'IFCBUILDINGSTOREY') + FACILITY_TYPES,
    'IFCSPACE': (('IFCBUILDINGSTOREY', 'IFCBUILDING', 'IFCSITE', 'IFCSPACE',
                  'IFCSPATIALZONE') + FACILITY_TYPES),
    'IFCSPATIALZONE': (('IFCPROJECT', 'IFCSITE', 'IFCBUILDING',
                        'IFCBUILDINGSTOREY', 'IFCSPATIALZONE') + FACILITY_TYPES),
    'IFCEXTERNALSPATIALELEMENT': (('IFCPROJECT', 'IFCSITE', 'IFCBUILDING',
                                   'IFCBUILDINGSTOREY') + FACILITY_TYPES),
}
for _t in FACILITY_TYPES:
    SPATIAL_PARENT[_t] = ('IFCPROJECT', 'IFCSITE') + FACILITY_TYPES

# IfcSpatialStructureElement puts CompositionType at attribute 8.  IfcSpatialZone
# and IfcExternalSpatialElement descend from IfcSpatialElement instead and put
# PredefinedType there, so reading one by position would record the other.
COMPOSITION_AT_8 = set(('IFCSITE', 'IFCBUILDING', 'IFCBUILDINGSTOREY',
                        'IFCSPACE') + FACILITY_TYPES)

# Entities kept during the parse pass (everything else is skipped for speed)
KEEP = {
    'IFCCARTESIANPOINT', 'IFCDIRECTION', 'IFCAXIS2PLACEMENT3D', 'IFCAXIS2PLACEMENT2D',
    'IFCLOCALPLACEMENT', 'IFCPRODUCTDEFINITIONSHAPE', 'IFCSHAPEREPRESENTATION',
    'IFCMAPPEDITEM', 'IFCREPRESENTATIONMAP', 'IFCCARTESIANTRANSFORMATIONOPERATOR3D',
    'IFCCARTESIANTRANSFORMATIONOPERATOR3DNONUNIFORM', 'IFCEXTRUDEDAREASOLID',
    'IFCREVOLVEDAREASOLID', 'IFCSURFACECURVESWEPTAREASOLID', 'IFCSWEPTDISKSOLID',
    'IFCPOLYGONALFACESET', 'IFCTRIANGULATEDFACESET', 'IFCCARTESIANPOINTLIST2D',
    'IFCCARTESIANPOINTLIST3D', 'IFCARBITRARYCLOSEDPROFILEDEF',
    'IFCARBITRARYPROFILEDEFWITHVOIDS', 'IFCARBITRARYOPENPROFILEDEF',
    'IFCRECTANGLEPROFILEDEF', 'IFCRECTANGLEHOLLOWPROFILEDEF', 'IFCCIRCLEPROFILEDEF',
    'IFCCIRCLEHOLLOWPROFILEDEF', 'IFCISHAPEPROFILEDEF', 'IFCINDEXEDPOLYCURVE',
    'IFCPOLYLINE', 'IFCGEOMETRICSET', 'IFCGEOMETRICCURVESET', 'IFCFACETEDBREP',
    'IFCCOMPOSITECURVE', 'IFCCOMPOSITECURVESEGMENT', 'IFCTRIMMEDCURVE',
    'IFCCIRCLE', 'IFCELLIPSE', 'IFCLINE',
    'IFCADVANCEDBREP', 'IFCCLOSEDSHELL', 'IFCOPENSHELL', 'IFCFACE',
    'IFCFACEOUTERBOUND', 'IFCFACEBOUND', 'IFCPOLYLOOP', 'IFCSHELLBASEDSURFACEMODEL',
    'IFCFACEBASEDSURFACEMODEL', 'IFCBOOLEANRESULT', 'IFCBOOLEANCLIPPINGRESULT',
    'IFCCSGSOLID', 'IFCBLOCK', 'IFCBOUNDINGBOX', 'IFCRELDEFINESBYTYPE',
    'IFCSIUNIT', 'IFCCONVERSIONBASEDUNIT', 'IFCMEASUREWITHUNIT',
    'IFCUNITASSIGNMENT',
}


def dms(s):
    """STEP compound angle (deg,min,sec[,millionths]) -> decimal degrees."""
    try:
        p = [float(x) for x in s.split(',') if x.strip() != '']
        if not p:
            return None
        d = p[0]
        m = p[1] if len(p) > 1 else 0
        sec = p[2] if len(p) > 2 else 0
        frac = p[3] / 1e6 if len(p) > 3 else 0
        return round((-1 if d < 0 else 1) * (abs(d) + m / 60 + (sec + frac) / 3600), 6)
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Model loading
# ----------------------------------------------------------------------------

CLOUD_ONLY = 0x400000        # FILE_ATTRIBUTE_RECALL_ON_DATA_ACCESS
OFFLINE = 0x1000             # FILE_ATTRIBUTE_OFFLINE


def is_cloud_only(path):
    """True for a OneDrive / cloud placeholder that is not on this disk yet."""
    try:
        a = os.stat(path).st_file_attributes
    except (AttributeError, OSError):
        return False
    return bool(a & (CLOUD_ONLY | OFFLINE))


def ensure_local(path, tries=4, delay=3.0):
    """Force a cloud-only file onto disk before the parse pass.

    OneDrive Files On-Demand hydrates a placeholder on first access.  While
    that is in flight a read can fail outright with OSError 22, which is how a
    package audit died on its first model with a message naming neither the
    cause nor the file.  Reading the first and last byte pulls the whole file
    down; the retry covers a hydration that has not finished yet.
    """
    err = None
    for i in range(tries):
        try:
            with open(path, 'rb') as f:
                f.read(4096)
                if os.path.getsize(path) > 4096:
                    f.seek(-1, os.SEEK_END)     # the last byte forces the rest
                    f.read(1)
            return
        except OSError as e:
            err = e
            # only a hydration that is still in flight gets better on a retry;
            # a permission or path error will not, so do not sit on it
            if i + 1 >= tries or not is_cloud_only(path):
                break
            time.sleep(delay * (i + 1))
    if is_cloud_only(path):
        raise IOError('stored in the cloud and could not be downloaded - in File '
                      'Explorer, right-click it and choose "Always keep on this '
                      'device", then run the audit again (%s)' % err)
    raise IOError('%s' % err)


class Model:
    """A parsed IFC file: only the entities needed for geolocation + geometry."""

    def __init__(self, path):
        self.path = path
        self.name = os.path.basename(path)
        self.ent = {}                 # id -> (TYPE, [args])
        self.schema = '?'
        self.unit_name = None         # e.g. 'MILLIMETRE'
        self.to_mm = None             # project length unit -> millimetres
        self.n_projects = 0           # IfcProject count; the apex of the hierarchy
        self.site = []                # [(lat, lon, elev, name)]
        self.site_place = []          # IfcSite ObjectPlacement ids
        self.has_address = True if False else False
        self.site_origin = None       # site placement translation, project units
        self.map_conv = None          # dict of IfcMapConversion parameters
        self.crs = None               # IfcProjectedCRS Name
        self.crs_id = None
        self.map_to_mm = 1000.0       # CRS map unit -> mm (metre by default)
        self.map_unit_name = 'METRE'
        self.true_north = None        # degrees, from the model context
        self.wcs_offset = None        # IfcGeometricRepresentationContext WCS origin
        self.elements = []            # [Element]
        self.guid_count = Counter()
        self.guid_detail = defaultdict(list)
        self.inst_type = {}           # element id -> IfcTypeObject id
        self.decomposed = set()       # ids that aggregate/nest children
        self.n_containers = 0         # geometry-less aggregates, audited via children
        self.project_ids = []         # IfcProject ids, in file order
        self.site_ids = []            # IfcSite ids, in file order
        self.spatial = {}             # id -> spatial record (site/building/storey/space)
        self.building_ids = []
        self.storey_ids = []
        self.space_ids = []
        self.agg_parent = {}          # child id -> parent, from IfcRelAggregates/Nests
        self.contained = {}           # element id -> the spatial element holding it
        self.n_contain_rels = 0       # IfcRelContainedInSpatialStructure count
        self.type_ids = []            # IfcTypeObject ids, in file order
        self.view_def = None          # ViewDefinition [...] from FILE_DESCRIPTION
        self.exchange_req = None      # ExchangeRequirement [...]
        self.coord_ref = None         # CoordinateReference [...]
        self.authoring_tool = None    # FILE_NAME originating system
        self.preprocessor = None      # FILE_NAME preprocessor version
        self.export_date = None       # FILE_NAME time stamp
        self.unhandled = Counter()
        self._bbcache = {}
        self._mcache = {}
        self._load()

    # -- parsing -------------------------------------------------------------

    def _load(self):
        ensure_local(self.path)
        ctx_ids = []
        proj_units = None
        raw_elems = []
        with open(self.path, 'r', encoding='utf-8', errors='replace') as f:
            in_data = False
            head = []
            for line in f:
                if not in_data:
                    head.append(line)
                    if 'DATA;' in line:
                        in_data = True
                        h = ''.join(head)
                        m = re.search(r"FILE_SCHEMA\s*\(\s*\(\s*'([^']+)'", h)
                        self.schema = m.group(1) if m else '?'
                        self._read_header(h)
                    continue
                if not line or line[0] != '#':
                    continue
                eq = line.find('=')
                if eq < 0:
                    continue
                lp = line.find('(', eq)
                if lp < 0:
                    continue
                typ = line[eq + 1:lp]
                rec = None

                if typ in KEEP:
                    rec = parse_record(line)
                    if rec:
                        self.ent[rec[0]] = (typ, split_args(rec[2]))
                    continue

                if typ == 'IFCPROJECT':
                    rec = parse_record(line)
                    a = split_args(rec[2])
                    self.n_projects += 1
                    self.project_ids.append(rec[0])
                    proj_units = ref(arg(a, 8))
                    ctx_ids += reflist(arg(a, 7))
                    self._count_guid(sval(arg(a, 0)), rec[0], typ)
                    continue
                if typ == 'IFCGEOMETRICREPRESENTATIONCONTEXT':
                    rec = parse_record(line)
                    self.ent[rec[0]] = (typ, split_args(rec[2]))
                    continue
                if typ == 'IFCSITE':
                    rec = parse_record(line)
                    a = split_args(rec[2])
                    lat = numtuple(arg(a, 9))
                    lon = numtuple(arg(a, 10))
                    self.site.append((
                        dms(','.join(str(v) for v in lat)) if lat else None,
                        dms(','.join(str(v) for v in lon)) if lon else None,
                        num(arg(a, 11)),
                        sval(arg(a, 2)) or sval(arg(a, 7)) or ''))
                    self.site_place.append(ref(arg(a, 5)))
                    self.site_ids.append(rec[0])
                    self._read_spatial(typ, rec[0], a)
                    if sval(arg(a, 12)) or sval(arg(a, 13)):
                        self.has_address = True
                    self._count_guid(sval(arg(a, 0)), rec[0], typ)
                    continue
                if typ in SPATIAL_TYPES:
                    # The spatial tree: what decides which level an element is
                    # on, and therefore whether a federated set stacks.  Held
                    # apart from self.elements because none of these are
                    # elements - they are the containers elements sit in.
                    rec = parse_record(line)
                    a = split_args(rec[2])
                    self._read_spatial(typ, rec[0], a)
                    self._count_guid(sval(arg(a, 0)), rec[0], typ)
                    continue
                if typ == 'IFCRELCONTAINEDINSPATIALSTRUCTURE':
                    rec = parse_record(line)
                    a = split_args(rec[2])
                    st = ref(arg(a, 5))
                    self.n_contain_rels += 1
                    for e in reflist(arg(a, 4)):
                        self.contained.setdefault(e, st)
                if typ == 'IFCPOSTALADDRESS':
                    self.has_address = True
                    continue
                if typ == 'IFCMAPCONVERSION':
                    a = split_args(parse_record(line)[2])
                    self.map_conv = {
                        'eastings': num(arg(a, 2)), 'northings': num(arg(a, 3)),
                        'height': num(arg(a, 4)), 'xaxis_abscissa': num(arg(a, 5)),
                        'xaxis_ordinate': num(arg(a, 6)), 'scale': num(arg(a, 7))}
                    continue
                if typ == 'IFCPROJECTEDCRS':
                    rec = parse_record(line)
                    self.ent[rec[0]] = (typ, split_args(rec[2]))
                    if self.crs is None:
                        self.crs_id = rec[0]
                        self.crs = sval(arg(self.ent[rec[0]][1], 0))
                    continue

                if typ in ('IFCRELAGGREGATES', 'IFCRELNESTS'):
                    rec = parse_record(line)
                    a = split_args(rec[2])
                    parent = ref(arg(a, 4))
                    if parent is not None:
                        if typ == 'IFCRELAGGREGATES':
                            # IfcRelNests is deliberately left out of
                            # self.decomposed: that set decides which
                            # geometry-less entities are audited through their
                            # parts instead, and a pipe with ports nested under
                            # it is not an assembly of those ports.
                            self.decomposed.add(parent)
                        for kid in reflist(arg(a, 5)):
                            # the child side, which Phase 1 never kept: it is
                            # what lets the hierarchy be walked from a storey
                            # up to the IfcProject, and what carries
                            # containment down from an assembly to its parts
                            self.agg_parent.setdefault(kid, parent)

                # any remaining rooted entity: GlobalId uniqueness + elements.
                # A rooted entity is 'IFCxxx(<22-char GlobalId>,<OwnerHistory|$>,...'
                # - the OwnerHistory check is what keeps IfcPropertySingleValue and
                # friends, whose first argument is also a string, out of the count.
                mg = RE_GUID.match(line, lp)
                if not mg or not is_rooted(typ):
                    continue
                guid = mg.group(1)
                eid = int(line[1:eq])
                self._count_guid(guid, eid, typ)
                if typ.endswith('TYPE') and not typ.startswith('IFCREL') \
                        and 'PROPERTY' not in typ and 'MATERIAL' not in typ:
                    # Type objects hold the PredefinedType an occurrence can
                    # inherit and the family name duplicate grading falls back
                    # to.  Skipping them left both lookups permanently empty.
                    self.ent[eid] = (typ, split_args(parse_record(line)[2]))
                    self.type_ids.append(eid)
                    continue
                if typ.endswith('TYPE') or typ.startswith('IFCREL') \
                        or 'PROPERTY' in typ or 'MATERIAL' in typ or typ in EXCLUDE:
                    continue
                raw_elems.append((eid, typ, line))

        self._resolve_units(proj_units)
        self._resolve_map_unit()
        self._resolve_context(ctx_ids)
        self._resolve_spatial()
        self._build_elements(raw_elems)
        if self.site_place and self.site_place[0] is not None:
            self.site_origin = self.placement(self.site_place[0])[1]

    def _read_header(self, h):
        """What the authoring tool declared about this export.

        FILE_DESCRIPTION carries the MVD the exporter claims to follow, and
        FILE_NAME carries which tool wrote the file.  Both decide how much of
        the model a receiving system is entitled to expect, and neither is
        visible anywhere in the model tree.
        """
        d = re.search(r"FILE_DESCRIPTION\s*\((.*?)\)\s*,\s*'[^']*'\s*\)",
                      h, re.S)
        desc = d.group(1) if d else h
        for rx, attr in ((RE_VIEWDEF, 'view_def'),
                         (RE_EXCHANGE, 'exchange_req'),
                         (RE_COORDREF, 'coord_ref')):
            m = rx.search(desc)
            if m:
                setattr(self, attr, m.group(1).strip() or None)
        n = re.search(r"FILE_NAME\s*\((.*?)\)\s*;", h, re.S)
        if n:
            a = split_args(n.group(1))
            self.export_date = sval(arg(a, 1))
            self.preprocessor = sval(arg(a, 4))
            self.authoring_tool = sval(arg(a, 5))

    def type_info(self, eid):
        """(PredefinedType, ElementType, type name) of an element's IfcTypeObject."""
        tid = self.inst_type.get(eid)
        e = self.ent.get(tid) if tid is not None else None
        if not e or not e[0].endswith('TYPE'):
            return None, None, None
        a = e[1]
        return (enum_val(arg(a, TYPE_PDT_INDEX)),
                sval(arg(a, TYPE_ELEMTYPE_INDEX)),
                sval(arg(a, 2)))

    IMPERIAL_MM = {'FOOT': 304.8, 'FEET': 304.8, 'INCH': 25.4, 'INCHES': 25.4,
                   'YARD': 914.4, 'MILE': 1609344.0}

    def _length_unit_mm(self, uid, depth=0):
        """A length-unit entity -> (millimetres per unit, display name)."""
        e = self.ent.get(uid)
        if not e or depth > 4:
            return None, None
        t, a = e
        if t == 'IFCSIUNIT':
            prefix = arg(a, 2).strip('.')
            prefix = '' if prefix in ('$', '*') else prefix
            base = arg(a, 3).strip('.')
            if base != 'METRE':
                return None, (base or None)
            return 1000.0 * SI_PREFIX.get(prefix, 1.0), (prefix + base)
        if t == 'IFCCONVERSIONBASEDUNIT':
            # attribute 1 is UnitType, 2 is Name, 3 is the IfcMeasureWithUnit factor
            name = (sval(arg(a, 2)) or '?').upper()
            mw = self.ent.get(ref(arg(a, 3)))
            if mw and mw[0] == 'IFCMEASUREWITHUNIT':
                v = RE_TUPLES.search(arg(mw[1], 0))
                base_mm, _ = self._length_unit_mm(ref(arg(mw[1], 1)), depth + 1)
                if v and base_mm:
                    try:
                        return float(v.group(1)) * base_mm, name
                    except ValueError:
                        pass
            return self.IMPERIAL_MM.get(name), name
        return None, None

    def _is_length_unit(self, uid):
        e = self.ent.get(uid)
        return bool(e) and e[0] in ('IFCSIUNIT', 'IFCCONVERSIONBASEDUNIT')             and '.LENGTHUNIT.' in arg(e[1], 1)

    def _read_spatial(self, typ, eid, a):
        """One spatial container: what it is called and where it sits.

        Elevation is read only for IfcBuildingStorey - attribute 9 is the
        storey elevation there and the site latitude on IfcSite, so reading it
        by position on anything else would record a latitude as a level.
        """
        rec = {'id': eid, 'class': typ,
               'name': sval(arg(a, 2)) or '',
               'long_name': sval(arg(a, 7)) or '',
               'composition': (enum_val(arg(a, 8))
                               if typ in COMPOSITION_AT_8 else None),
               'place_id': ref(arg(a, 5)),
               'elevation': num(arg(a, 9)) if typ == 'IFCBUILDINGSTOREY' else None,
               'z': None}
        self.spatial[eid] = rec
        if typ == 'IFCBUILDING':
            self.building_ids.append(eid)
        elif typ == 'IFCBUILDINGSTOREY':
            self.storey_ids.append(eid)
        elif typ == 'IFCSPACE':
            self.space_ids.append(eid)

    def _resolve_spatial(self):
        """Where each container actually sits, through its placement chain.

        The Elevation attribute is relative to whatever datum the authoring
        model used, so it is not comparable between two discipline models.  The
        placement chain resolves to absolute project coordinates, which is the
        number two models can be held against each other on.
        """
        for rec in self.spatial.values():
            pid = rec['place_id']
            # only a real IfcLocalPlacement chain resolves; anything else
            # would come back as the identity and read as a storey at zero,
            # which is a level the file never stated
            if pid is None or self.ent.get(pid, ('',))[0] != 'IFCLOCALPLACEMENT':
                continue
            rec['z'] = self.placement(pid)[1][2]

    def _count_guid(self, guid, eid, typ):
        """Tally a GlobalId and remember who used it, so counts and ids agree."""
        if not guid:
            return
        self.guid_count[guid] += 1
        if len(self.guid_detail[guid]) < 6:
            self.guid_detail[guid].append((eid, typ))

    def _resolve_units(self, proj_units):
        """Length unit of the IfcProject, not merely the first one in the file."""
        cands = []
        if proj_units is not None and proj_units in self.ent:
            cands = [u for u in reflist(arg(self.ent[proj_units][1], 0))
                     if self._is_length_unit(u)]
        if not cands:
            # no usable IfcUnitAssignment: fall back to any length unit in the
            # file, but never the one the IfcProjectedCRS declares for the map
            skip = set()
            if self.crs_id is not None and self.crs_id in self.ent:
                mu = ref(arg(self.ent[self.crs_id][1], 6))
                if mu is not None:
                    skip.add(mu)
            cands = [i for i in self.ent if i not in skip and self._is_length_unit(i)]
            cands.sort()
        for uid in cands:
            f, nm = self._length_unit_mm(uid)
            if nm and self.unit_name is None:
                self.unit_name = nm
            if f:
                self.unit_name = nm
                self.to_mm = f
                return

    def _resolve_map_unit(self):
        """Length unit the IfcProjectedCRS uses, so map deltas can be read in mm."""
        if self.crs_id is None or self.crs_id not in self.ent:
            return
        mu = ref(arg(self.ent[self.crs_id][1], 6))
        if mu is None:
            return
        f, nm = self._length_unit_mm(mu)
        if f:
            self.map_to_mm = f
            self.map_unit_name = nm

    def _resolve_context(self, ctx_ids):
        for cid in ctx_ids:
            e = self.ent.get(cid)
            if not e or e[0] != 'IFCGEOMETRICREPRESENTATIONCONTEXT':
                continue
            a = e[1]
            tn = ref(arg(a, 5))
            if tn is not None:
                d = self._direction(tn)
                if d:
                    self.true_north = round(math.degrees(math.atan2(d[0], d[1])), 6)
            wcs = ref(arg(a, 4))
            if wcs is not None:
                M = self._axis3d(wcs)
                if M and any(abs(c) > 1e-9 for c in M[1]):
                    self.wcs_offset = M[1]
            break

    def _build_elements(self, raw_elems):
        fam = schema_family(self.schema)
        for eid, typ, line in raw_elems:
            a = split_args(parse_record(line)[2])
            pdt, pdt_how = elem_pdt(typ, a, fam)
            name = sval(arg(a, 2)) or ''
            otype = sval(arg(a, 4)) or ''
            place = ref(arg(a, 5))
            shape = ref(arg(a, 6))
            tag = sval(arg(a, 7)) or ''
            if place is not None and self.ent.get(place, ('',))[0] != 'IFCLOCALPLACEMENT':
                place = None
            # Aggregate containers (IfcStair, IfcRamp, IfcRoof, IfcElementAssembly...)
            # carry no body of their own; their placement is usually the storey
            # origin, which would read as a false coincidence.  Audit the parts.
            if shape is None and eid in self.decomposed:
                self.n_containers += 1
                continue
            self.elements.append(
                Element(eid, typ, name, otype, tag, place, shape, pdt, pdt_how))
        # instance -> type object, for a family-name fallback
        for (t, a) in list(self.ent.values()):
            if t == 'IFCRELDEFINESBYTYPE':
                tid = ref(arg(a, 5))
                for oid in reflist(arg(a, 4)):
                    self.inst_type[oid] = tid

    # -- geometry ------------------------------------------------------------

    def _pt(self, i):
        e = self.ent.get(i)
        return numtuple(arg(e[1], 0)) if e and e[0] == 'IFCCARTESIANPOINT' else None

    def _direction(self, i):
        e = self.ent.get(i)
        return numtuple(arg(e[1], 0)) if e and e[0] == 'IFCDIRECTION' else None

    def _axis3d(self, i):
        """IfcAxis2Placement2D/3D -> (R,t)."""
        if i is None:
            return IDENT
        c = self._mcache.get(i)
        if c is not None:
            return c
        e = self.ent.get(i)
        if not e:
            return IDENT
        a = e[1]
        if e[0] == 'IFCAXIS2PLACEMENT3D':
            M = frame(self._pt(ref(arg(a, 0))), self._direction(ref(arg(a, 1))),
                      self._direction(ref(arg(a, 2))))
        elif e[0] == 'IFCAXIS2PLACEMENT2D':
            M = frame(self._pt(ref(arg(a, 0))), None, self._direction(ref(arg(a, 1))))
        else:
            M = IDENT
        self._mcache[i] = M
        return M

    def placement(self, i, depth=0):
        """Absolute (R,t) of an IfcLocalPlacement chain, rotation included."""
        if i is None or depth > 64:
            return IDENT
        key = ('lp', i)
        c = self._mcache.get(key)
        if c is not None:
            return c
        e = self.ent.get(i)
        if not e or e[0] != 'IFCLOCALPLACEMENT':
            return IDENT
        a = e[1]
        self._mcache[key] = IDENT          # cycle guard
        rel = ref(arg(a, 0))
        M = mmul(self.placement(rel, depth + 1), self._axis3d(ref(arg(a, 1))))
        self._mcache[key] = M
        return M

    def _operator(self, i):
        """IfcCartesianTransformationOperator3D -> (R,t)."""
        if i is None:
            return IDENT
        e = self.ent.get(i)
        if not e:
            return IDENT
        a = e[1]
        M = frame(self._pt(ref(arg(a, 2))), self._direction(ref(arg(a, 4))),
                  self._direction(ref(arg(a, 0))))
        s = num(arg(a, 3))
        if s is not None and abs(s - 1.0) > 1e-12:
            M = (tuple(v * s for v in M[0]), M[1])
        return M

    def _profile_bb(self, i, depth):
        """Local 2D bbox of a profile, in the profile's own plane (z = 0)."""
        e = self.ent.get(i)
        if not e:
            if i is not None:
                self.unhandled['(profile not parsed)'] += 1
            return None
        t, a = e
        if t in ('IFCARBITRARYCLOSEDPROFILEDEF', 'IFCARBITRARYPROFILEDEFWITHVOIDS',
                 'IFCARBITRARYOPENPROFILEDEF'):
            return self._curve_bb(ref(arg(a, 2)), depth + 1)
        if t in ('IFCRECTANGLEPROFILEDEF', 'IFCRECTANGLEHOLLOWPROFILEDEF'):
            x = num(arg(a, 3)) or 0.
            y = num(arg(a, 4)) or 0.
            b = (-x / 2, -y / 2, 0., x / 2, y / 2, 0.)
            return bb_transform(b, self._axis3d(ref(arg(a, 2))))
        if t in ('IFCCIRCLEPROFILEDEF', 'IFCCIRCLEHOLLOWPROFILEDEF'):
            r = num(arg(a, 3)) or 0.
            return bb_transform((-r, -r, 0., r, r, 0.), self._axis3d(ref(arg(a, 2))))
        if t == 'IFCISHAPEPROFILEDEF':
            w = num(arg(a, 3)) or 0.
            h = num(arg(a, 4)) or 0.
            b = (-w / 2, -h / 2, 0., w / 2, h / 2, 0.)
            return bb_transform(b, self._axis3d(ref(arg(a, 2))))
        self.unhandled[t] += 1
        return None

    def _curve_bb(self, i, depth):
        if depth > 24:
            return None
        e = self.ent.get(i)
        if not e:
            # an entity outside KEEP is never parsed, so it used to disappear
            # here without being counted - that is how a fifth of a model
            # resolved to nothing while 'unresolved' stayed empty
            if i is not None:
                self.unhandled['(curve not parsed)'] += 1
            return None
        t, a = e
        if t == 'IFCINDEXEDPOLYCURVE':
            pl = self.ent.get(ref(arg(a, 0)))
            return bb_points(point_rows(arg(pl[1], 0))) if pl else None
        if t == 'IFCPOLYLINE':
            return bb_points(p for p in (self._pt(r) for r in reflist(arg(a, 0))) if p)
        if t == 'IFCPOLYLOOP':
            return bb_points(p for p in (self._pt(r) for r in reflist(arg(a, 0))) if p)

        # Revit writes rolled and formed steel sections as a composite curve of
        # line and arc segments, so a channel or angle has no extent at all
        # without these.
        if t == 'IFCCOMPOSITECURVE':
            b = None
            for r in reflist(arg(a, 0)):
                b = bb_union(b, self._curve_bb(r, depth + 1))
            return b

        if t == 'IFCCOMPOSITECURVESEGMENT':
            return self._curve_bb(ref(arg(a, 2)), depth + 1)

        if t == 'IFCTRIMMEDCURVE':
            # cartesian trim points bound the arc exactly; a parametric trim
            # falls back to the whole basis curve, which over-states an arc by
            # at most its radius - harmless at bounding-box resolution
            pts = [p for p in (self._pt(r) for r in
                               reflist(arg(a, 1)) + reflist(arg(a, 2))) if p]
            if pts:
                return bb_points(pts)
            return self._curve_bb(ref(arg(a, 0)), depth + 1)

        if t in ('IFCCIRCLE', 'IFCELLIPSE'):
            c = self._axis3d(ref(arg(a, 0)))[1]
            r1 = num(arg(a, 1)) or 0.
            r2 = (num(arg(a, 2)) or r1) if t == 'IFCELLIPSE' else r1
            rz = max(r1, r2)
            return (c[0] - r1, c[1] - r2, c[2] - rz,
                    c[0] + r1, c[1] + r2, c[2] + rz)

        if t == 'IFCLINE':
            # unbounded on its own; only its origin is a usable extent
            p = self._pt(ref(arg(a, 0)))
            return bb_points([p]) if p else None

        self.unhandled[t] += 1
        return None

    def item_bb(self, i, depth=0):
        """Bounding box of a representation item, in the item's own space."""
        if i is None or depth > 32:
            return None
        e = self.ent.get(i)
        if not e:
            return None
        t, a = e

        if t == 'IFCMAPPEDITEM':
            rm = self.ent.get(ref(arg(a, 0)))
            if not rm:
                return None
            M = mmul(self._operator(ref(arg(a, 1))), self._axis3d(ref(arg(rm[1], 0))))
            return bb_transform(self.representation_bb(ref(arg(rm[1], 1)), depth + 1), M)

        if t == 'IFCEXTRUDEDAREASOLID':
            p = self._profile_bb(ref(arg(a, 0)), depth)
            if p is None:
                return None
            d = _norm(_v3(self._direction(ref(arg(a, 2))))) or (0., 0., 1.)
            depth_v = num(arg(a, 3)) or 0.
            far = (p[0] + d[0] * depth_v, p[1] + d[1] * depth_v, p[2] + d[2] * depth_v,
                   p[3] + d[0] * depth_v, p[4] + d[1] * depth_v, p[5] + d[2] * depth_v)
            return bb_transform(bb_union(p, far), self._axis3d(ref(arg(a, 1))))

        if t in ('IFCREVOLVEDAREASOLID', 'IFCSURFACECURVESWEPTAREASOLID'):
            self.unhandled[t] += 1
            p = self._profile_bb(ref(arg(a, 0)), depth)
            return bb_transform(p, self._axis3d(ref(arg(a, 1)))) if p else None

        if t == 'IFCSWEPTDISKSOLID':
            c = self._curve_bb(ref(arg(a, 0)), depth + 1)
            r = num(arg(a, 1)) or 0.
            return (c[0] - r, c[1] - r, c[2] - r, c[3] + r, c[4] + r, c[5] + r) if c else None

        if t in ('IFCPOLYGONALFACESET', 'IFCTRIANGULATEDFACESET'):
            pl = self.ent.get(ref(arg(a, 0)))
            return bb_points(point_rows(arg(pl[1], 0))) if pl else None

        if t == 'IFCBOUNDINGBOX':
            o = self._pt(ref(arg(a, 0))) or (0., 0., 0.)
            x = num(arg(a, 1)) or 0.
            y = num(arg(a, 2)) or 0.
            z = num(arg(a, 3)) or 0.
            return (o[0], o[1], o[2], o[0] + x, o[1] + y, o[2] + z)

        if t in ('IFCBOOLEANRESULT', 'IFCBOOLEANCLIPPINGRESULT'):
            # First operand only: the second is a cutting tool and may be huge.
            # Revit writes one boolean per opening, chained through FirstOperand,
            # so a floor slab with 41 penetrations nests 41 deep.  Walk that
            # chain iteratively: recursing hits the runaway-recursion guard and
            # the element is then reported as having no geometry at all, which
            # lands it on the placement origin and looks like a floating element.
            j, hops = ref(arg(a, 1)), 0
            while hops < 4096:
                e2 = self.ent.get(j)
                if not e2 or e2[0] not in ('IFCBOOLEANRESULT',
                                           'IFCBOOLEANCLIPPINGRESULT'):
                    break
                j = ref(arg(e2[1], 1))
                hops += 1
            return self.item_bb(j, depth + 1)

        if t in ('IFCGEOMETRICSET', 'IFCGEOMETRICCURVESET', 'IFCCLOSEDSHELL',
                 'IFCOPENSHELL', 'IFCSHELLBASEDSURFACEMODEL', 'IFCFACEBASEDSURFACEMODEL'):
            b = None
            for r in reflist(arg(a, 0)):
                b = bb_union(b, self.item_bb(r, depth + 1))
            return b

        if t in ('IFCFACETEDBREP', 'IFCADVANCEDBREP', 'IFCCSGSOLID'):
            return self.item_bb(ref(arg(a, 0)), depth + 1)

        if t == 'IFCFACE':
            b = None
            for r in reflist(arg(a, 0)):
                b = bb_union(b, self.item_bb(r, depth + 1))
            return b

        if t in ('IFCFACEOUTERBOUND', 'IFCFACEBOUND'):
            return self._curve_bb(ref(arg(a, 0)), depth + 1)

        if t in ('IFCPOLYLINE', 'IFCPOLYLOOP', 'IFCINDEXEDPOLYCURVE'):
            return self._curve_bb(i, depth + 1)

        self.unhandled[t] += 1
        return None

    def representation_bb(self, i, depth=0):
        """Bounding box of an IfcShapeRepresentation, in its own space."""
        e = self.ent.get(i)
        if not e or e[0] != 'IFCSHAPEREPRESENTATION' or depth > 32:
            return None
        b = None
        for r in reflist(arg(e[1], 3)):
            b = bb_union(b, self.item_bb(r, depth + 1))
        return b

    def body_bb(self, shape_id):
        """Local bbox of the Body representation of an IfcProductDefinitionShape."""
        if shape_id is None:
            return None
        c = self._bbcache.get(shape_id)
        if c is not None:
            return c[0]
        e = self.ent.get(shape_id)
        if not e or e[0] != 'IFCPRODUCTDEFINITIONSHAPE':
            return None
        reps = reflist(arg(e[1], 2))
        chosen = []
        for rid in reps:
            r = self.ent.get(rid)
            if not r or r[0] != 'IFCSHAPEREPRESENTATION':
                continue
            ident = sval(arg(r[1], 1)) or ''
            if ident == 'Body':
                chosen = [rid]
                break
            if ident not in NON_BODY:
                chosen.append(rid)
        if not chosen:
            chosen = [rid for rid in reps
                      if (sval(arg(self.ent[rid][1], 1)) or '') != 'Axis'
                      and rid in self.ent]
        b = None
        for rid in chosen:
            b = bb_union(b, self.representation_bb(rid))
        self._bbcache[shape_id] = (b,)
        return b


class Element:
    __slots__ = ('id', 'ifc_class', 'name', 'object_type', 'tag', 'place_id',
                 'shape_id', 'bbox', 'source', 'predefined', 'pdt_source')

    def __init__(self, eid, cls, name, otype, tag, place_id, shape_id,
                 predefined=None, pdt_source='index'):
        self.id = eid
        self.ifc_class = cls
        self.name = name
        self.object_type = otype
        self.tag = tag
        self.place_id = place_id
        self.shape_id = shape_id
        self.bbox = None
        self.source = 'none'    # 'body' | 'placement' | 'none'
        self.predefined = predefined    # PredefinedType enum, None when absent
        self.pdt_source = pdt_source    # 'index' | 'scan' | 'n/a'

    def type_key(self, model):
        """The 'same element / family name' identity used for duplicate grading."""
        if self.object_type:
            return re.sub(r'\s*:\s*', ':', self.object_type.strip())
        tid = model.inst_type.get(self.id)
        if tid is not None and tid in model.ent:
            n = sval(arg(model.ent[tid][1], 2))
            if n:
                return re.sub(r'\s*:\s*', ':', n.strip())
        return re.sub(r'\s*:\s*', ':', (self.name or '').strip())

    def label(self):
        return self.object_type or self.name or self.ifc_class


# ----------------------------------------------------------------------------
# Grouping helpers
# ----------------------------------------------------------------------------

class DSU:
    def __init__(self):
        self.p = {}

    def find(self, x):
        self.p.setdefault(x, x)
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.p[ra] = rb


def sweep_pairs(items):
    """Yield index pairs whose bboxes overlap in x (cheap prefilter)."""
    order = sorted(range(len(items)), key=lambda i: items[i].bbox[0])
    active = []
    for i in order:
        lo = items[i].bbox[0]
        active = [j for j in active if items[j].bbox[3] >= lo]
        for j in active:
            yield j, i
        active.append(i)


def grid_pairs(items, cell, cell_cap=1000):
    """Yield index pairs sharing a grid cell.  Oversized items are reported back."""
    buckets = defaultdict(list)
    oversize = []
    for idx, e in enumerate(items):
        b = e.bbox
        nx = int(b[3] // cell) - int(b[0] // cell) + 1
        ny = int(b[4] // cell) - int(b[1] // cell) + 1
        nz = int(b[5] // cell) - int(b[2] // cell) + 1
        if nx * ny * nz > cell_cap:
            oversize.append(idx)
            continue
        for ix in range(int(b[0] // cell), int(b[3] // cell) + 1):
            for iy in range(int(b[1] // cell), int(b[4] // cell) + 1):
                for iz in range(int(b[2] // cell), int(b[5] // cell) + 1):
                    buckets[(ix, iy, iz)].append(idx)
    seen = set()
    for cellitems in buckets.values():
        n = len(cellitems)
        for i in range(n):
            a = cellitems[i]
            for j in range(i + 1, n):
                p = (a, cellitems[j]) if a < cellitems[j] else (cellitems[j], a)
                if p not in seen:
                    seen.add(p)
                    yield p
    return oversize


# ----------------------------------------------------------------------------
# Duplicate grading
# ----------------------------------------------------------------------------

def find_duplicates(model, elems, tol, iou_dup, iou_prob):
    """
    Grade geometric duplicates.  A pair is only ever a duplicate candidate when
    it shares BOTH the IFC class and the type / family name; overlap alone is
    never enough.  Returns (groups, n_pairs_tested).
    """
    by_key = defaultdict(list)
    for e in elems:
        by_key[(e.ifc_class, e.type_key(model))].append(e)

    groups = []
    tested = 0
    for (cls, tkey), items in by_key.items():
        if len(items) < 2:
            continue
        dsu = DSU()
        verdicts = {}
        for j, i in sweep_pairs(items):
            a, b = items[j], items[i]
            tested += 1
            if a.source == 'body' and b.source == 'body':
                iou = bb_iou(a.bbox, b.bbox, pad=tol)
                if iou >= iou_dup:
                    v = 'DUPLICATE'
                elif iou >= iou_prob:
                    v = 'PROBABLE'
                else:
                    continue
                ev = 'IoU %.2f' % iou
            else:
                ca, cb = bb_centre(a.bbox), bb_centre(b.bbox)
                if max(abs(ca[k] - cb[k]) for k in range(3)) > tol:
                    continue
                v = 'PROBABLE'
                ev = 'coincident placement, geometry not resolved'
            dsu.union(a.id, b.id)
            r = dsu.find(a.id)
            prev = verdicts.get(r)
            verdicts[r] = (v, ev) if prev is None or (prev[0] == 'PROBABLE' and v == 'DUPLICATE') else prev

        clusters = defaultdict(list)
        for e in items:
            if e.id in dsu.p:
                clusters[dsu.find(e.id)].append(e)
        for root, members in clusters.items():
            if len(members) < 2:
                continue
            v, ev = verdicts.get(root, ('PROBABLE', ''))
            bb = None
            for m in members:
                bb = bb_union(bb, m.bbox)
            groups.append({
                'verdict': v, 'class': cls, 'type': tkey, 'count': len(members),
                'evidence': ev, 'ids': sorted(m.id for m in members)[:12],
                'tags': sorted({m.tag for m in members if m.tag})[:12],
                'centre': bb_centre(bb),
                'geometry': 'body' if all(m.source == 'body' for m in members) else 'placement',
            })
    order = {'DUPLICATE': 0, 'PROBABLE': 1}
    groups.sort(key=lambda g: (order[g['verdict']], -g['count']))
    return groups, tested


def find_interferences(model, elems, frac, dup_ids):
    """
    Overlapping pairs that are NOT duplicates - different class or different
    type/family name.  Reported separately; these are coordination issues, not
    duplicates.  AABB-based, so coarse: this is a smell test, not clash detection.
    """
    items = [e for e in elems if e.source == 'body' and bb_vol(e.bbox) > 0]
    if len(items) < 2:
        return [], 0
    diags = sorted(bb_diag(e.bbox) for e in items)
    cell = max(diags[len(diags) // 2], 1.0) * 2
    hits = []
    gen = grid_pairs(items, cell)
    oversize = []
    try:
        while True:
            i, j = next(gen)
            a, b = items[i], items[j]
            if a.ifc_class == b.ifc_class and a.type_key(model) == b.type_key(model):
                continue          # same identity -> handled by the duplicate pass
            if a.id in dup_ids and b.id in dup_ids:
                continue
            iv = bb_inter_vol(a.bbox, b.bbox)
            if iv <= 0:
                continue
            small = min(bb_vol(a.bbox), bb_vol(b.bbox))
            if small <= 0 or iv / small < frac:
                continue
            hits.append({'a': a.id, 'b': b.id, 'a_class': a.ifc_class,
                         'b_class': b.ifc_class, 'a_type': a.label()[:60],
                         'b_type': b.label()[:60], 'overlap_frac': round(iv / small, 3)})
    except StopIteration as stop:
        oversize = stop.value or []
    hits.sort(key=lambda h: -h['overlap_frac'])
    return hits, len(oversize)


# ----------------------------------------------------------------------------
# Floating / out-of-envelope elements
# ----------------------------------------------------------------------------

def median(vals):
    v = sorted(vals)
    n = len(v)
    if not n:
        return 0.0
    return v[n // 2] if n % 2 else (v[n // 2 - 1] + v[n // 2]) / 2.0


def robust_limit(d, k, floor):
    """
    median + k * MAD, the standard robust outlier fence.

    MAD tolerates up to 50% contamination, so a cluster of stray elements
    cannot inflate the limit until it hides itself - which is exactly how a
    percentile envelope fails.  `floor` keeps tiny or perfectly-stacked models
    (where MAD collapses to zero) from flagging everything.
    """
    m = median(d)
    mad = median([abs(x - m) for x in d]) * 1.4826
    return max(m + k * mad, floor), m, mad


def find_floating(elems, centres, u, opt):
    """
    Flag elements anomalously far from the model, in plan and in elevation.

    Distances are measured from a robust (median) model centre.  The default
    limits are statistical; --float-xy / --float-z override them with an
    absolute distance in metres when you already know the model.
    """
    if not centres:
        return [], None, None
    to_m = u / 1000.0                                   # project units -> metres
    cx = median([c[0] for c in centres])
    cy = median([c[1] for c in centres])
    cz = median([c[2] for c in centres])
    dp = [math.hypot(c[0] - cx, c[1] - cy) * to_m for c in centres]
    dz = [abs(c[2] - cz) * to_m for c in centres]

    if opt.float_xy is not None:
        thr_p, how_p = opt.float_xy, 'set'
    else:
        thr_p, _, _ = robust_limit(dp, opt.float_k, opt.float_min)
        how_p = 'auto'
    if opt.float_z is not None:
        thr_z, how_z = opt.float_z, 'set'
    else:
        thr_z, _, _ = robust_limit(dz, opt.float_k, opt.float_min)
        how_z = 'auto'

    # the spread of everything the fence accepted - the yardstick for 'far'
    keep_p = [p for p, v in zip(dp, dz) if p <= thr_p and v <= thr_z]
    keep_z = [v for p, v in zip(dp, dz) if p <= thr_p and v <= thr_z]
    bulk_p = max(keep_p) if keep_p else thr_p
    bulk_z = max(keep_z) if keep_z else thr_z

    out = []
    for e, pd, vd in zip(elems, dp, dz):
        if pd <= thr_p and vd <= thr_z:
            continue
        why = []
        ratio = 0.0
        if pd > thr_p:
            why.append('%.0f m from centre in plan' % pd)
            ratio = max(ratio, pd / bulk_p if bulk_p > 1e-9 else float('inf'))
        if vd > thr_z:
            why.append('%.1f m from centre vertically' % vd)
            ratio = max(ratio, vd / bulk_z if bulk_z > 1e-9 else float('inf'))
        detached = ratio > opt.float_detach
        out.append({'id': e.id, 'class': e.ifc_class, 'type': e.label()[:70],
                    'plan_m': round(pd, 1), 'vert_m': round(vd, 1),
                    'reason': ' and '.join(why),
                    'grade': FIX if detached else REVIEW,
                    'spread_ratio': round(ratio, 1) if ratio != float('inf') else None,
                    'clear_m': round(max(pd - bulk_p, vd - bulk_z), 1),
                    'verdict': 'detached from the model' if detached
                               else 'within reach of the model - check it '
                                    'against the architectural and structural '
                                    'envelope'})
    out.sort(key=lambda r: -(r['plan_m'] ** 2 + r['vert_m'] ** 2))
    thresholds = {'plan_m': round(thr_p, 1), 'vertical_m': round(thr_z, 1),
                  'plan_source': how_p, 'vertical_source': how_z,
                  'bulk_plan_m': round(bulk_p, 1), 'bulk_vertical_m': round(bulk_z, 1),
                  'median_plan_m': round(median(dp), 1),
                  'median_vertical_m': round(median(dz), 1)}
    return out, (cx, cy, cz), thresholds


# ----------------------------------------------------------------------------
# Spatial structure
#
# What decides whether a federated set stacks, and the one part of this tool
# no regional profile changes: every package in every country needs its
# elements on a storey, its storeys agreeing between the disciplines, and its
# tree rooted at the IfcProject.  Phase 1 could only report that IfcProject
# and IfcSite were present; with IfcRelAggregates now read from both sides the
# chain between them is walked rather than assumed.
# ----------------------------------------------------------------------------

def spatial_name(rec):
    """What to call a container in a report: its Name, else its LongName."""
    return (rec.get('name') or rec.get('long_name') or
            '(unnamed %s)' % ifc_name(rec.get('class', '?')))


def _chain_up(parent_of, eid, stop=64):
    """The parent chain above an id, nearest first, cycles cut."""
    out = []
    seen = set([eid])
    cur = parent_of.get(eid)
    while cur is not None and cur not in seen and len(out) < stop:
        out.append(cur)
        seen.add(cur)
        cur = parent_of.get(cur)
    return out


def audit_hierarchy(m):
    """Is the tree rooted the way IFC says it must be?

    Presence was all Phase 1 could afford.  This is the structural question:
    IfcProject at the apex with nothing above it, IfcSite aggregated into it,
    IfcBuilding into a site, IfcBuildingStorey into a building.  A receiving
    system walks that chain to decide what belongs to what, so a storey
    hanging off nothing is invisible to it however well the storey itself is
    filled in.
    """
    problems = []
    if m.spatial and not m.agg_parent:
        return {'ok': False, 'orphans': len(m.spatial),
                'problems': ['no IfcRelAggregates in the file, so nothing '
                             'states which site, building or storey anything '
                             'belongs to']}

    for pid in m.project_ids:
        if pid in m.agg_parent:
            up = m.agg_parent[pid]
            problems.append('IfcProject is aggregated into %s, so it is not '
                            'the apex of the hierarchy'
                            % ifc_name((m.spatial.get(up) or {}).get('class', '?')))

    orphans = 0
    for rec in sorted(m.spatial.values(), key=lambda r: r['id']):
        want = SPATIAL_PARENT.get(rec['class'], ())
        pid = m.agg_parent.get(rec['id'])
        if pid is None:
            orphans += 1
            if len(problems) < 40:
                problems.append('%s %s is not aggregated into anything'
                                % (ifc_name(rec['class']), spatial_name(rec)))
            continue
        got = ('IFCPROJECT' if pid in m.project_ids
               else (m.spatial.get(pid) or {}).get('class', '?'))
        if got not in want and len(problems) < 40:
            problems.append('%s %s hangs off %s, not %s'
                            % (ifc_name(rec['class']), spatial_name(rec),
                               ifc_name(got),
                               ' or '.join(ifc_name(w) for w in want)))
    return {'ok': not problems, 'problems': problems[:40], 'orphans': orphans}


def storey_of(m, eid):
    """(container id, container class, storey id) for one element.

    Containment is inherited down a decomposition: the members of a curtain
    wall and the flights of a stair appear in no
    IfcRelContainedInSpatialStructure of their own - their assembly does, and
    they belong to whatever contains it.  Reading only the direct relation
    would report every one of those parts as loose in the file.
    """
    cid = m.contained.get(eid)
    if cid is None:
        for up in _chain_up(m.agg_parent, eid):
            if up in m.contained:
                cid = m.contained[up]
                break
    if cid is None:
        return None, None, None
    rec = m.spatial.get(cid)
    if rec is None:
        # the relation names a container this parse did not keep
        return cid, '?', None
    if rec['class'] == 'IFCBUILDINGSTOREY':
        return cid, rec['class'], cid
    # an element contained in a space is on that space's storey
    for up in _chain_up(m.agg_parent, cid):
        r = m.spatial.get(up)
        if r and r['class'] == 'IFCBUILDINGSTOREY':
            return cid, rec['class'], up
    return cid, rec['class'], None


def audit_spatial(m, elems, u):
    """The spatial structure of one model, and what hangs off it.

    Three numbers are kept per storey, because they are three different
    things and only one of them compares between models:

      elevation_m  the Elevation attribute, relative to whatever datum the
                   authoring model used - not comparable
      z_m          the placement chain resolved to project coordinates -
                   comparable only while every model shares them
      level_m      z_m plus the height the model carries in IfcMapConversion,
                   which is the storey in the survey datum

    level_m is the one the package is held against.  A Revit export made on
    shared coordinates puts the survey offset in the IfcSite placement and
    leaves MapConversion at zero; one made on the survey point puts it in
    MapConversion and leaves the placement at zero.  Both are correct and the
    two land on the same real-world level - but their raw project Z differs by
    the whole offset, so comparing z_m would report every storey of a
    correctly-built package as a disagreement.
    """
    me = lambda v: None if v is None else round(v * u / 1000.0, 4)
    mc = m.map_conv or {}
    # map unit -> metres, so the MapConversion height reads in metres whatever
    # unit the CRS is declared in
    datum_h = (mc.get('height') or 0.0) * (m.map_to_mm or 1000.0) / 1000.0

    storeys = []
    for sid in m.storey_ids:
        rec = m.spatial[sid]
        z = me(rec['z'])
        storeys.append({'id': sid, 'name': spatial_name(rec),
                        'long_name': rec['long_name'],
                        'elevation_m': me(rec['elevation']),
                        'z_m': z,
                        'level_m': None if z is None else round(z + datum_h, 4),
                        'composition': rec['composition'],
                        'n_elements': 0, 'n_spaces': 0})
    by_id = dict((s['id'], s) for s in storeys)
    storeys.sort(key=lambda s: (s['z_m'] is None,
                                s['z_m'] if s['z_m'] is not None else 0.0))

    # -- spaces: which storey each room is on -------------------------------
    loose_spaces = []
    for sp in m.space_ids:
        host = None
        for up in _chain_up(m.agg_parent, sp):
            r = m.spatial.get(up)
            if r and r['class'] == 'IFCBUILDINGSTOREY':
                host = up
                break
        if host in by_id:
            by_id[host]['n_spaces'] += 1
        else:
            loose_spaces.append(spatial_name(m.spatial[sp]))

    # -- every element: which container holds it ----------------------------
    counts = Counter()
    loose = []
    above = []
    for e in elems:
        cid, ccls, sid = storey_of(m, e.id)
        if sid is not None:
            counts['storey'] += 1
            if sid in by_id:
                by_id[sid]['n_elements'] += 1
            continue
        if cid is None:
            counts['loose'] += 1
            if len(loose) < 2000:
                loose.append({'id': e.id, 'class': e.ifc_class,
                              'type': e.type_key(m), 'container': '(none)'})
            continue
        counts['above'] += 1
        rec = m.spatial.get(cid)
        if len(above) < 2000:
            if rec:
                held_by = '%s %s' % (ifc_name(rec['class']), spatial_name(rec))
            else:
                held_by = 'an entity this tool does not read'
            above.append({'id': e.id, 'class': e.ifc_class,
                          'type': e.type_key(m), 'container': held_by})

    return {
        'hierarchy': audit_hierarchy(m),
        'n_buildings': len(m.building_ids),
        'n_storeys': len(m.storey_ids),
        'n_spaces': len(m.space_ids),
        'n_contain_rels': m.n_contain_rels,
        'datum_height_m': round(datum_h, 4),
        'storeys': storeys,
        'spaces_outside_storey': loose_spaces[:40],
        'n_spaces_outside_storey': len(loose_spaces),
        'n_in_storey': counts['storey'],
        'n_above_storey': counts['above'],
        'n_loose': counts['loose'],
        'loose': loose,
        'loose_by_class': Counter(r['class'] for r in loose).most_common(12),
        'above_by_container': Counter(r['container'] for r in above).most_common(12),
        'above_storey': above,
    }


# ----------------------------------------------------------------------------
# Storeys across the package
#
# The highest-value item in Phase 2, and the reason the tree is worth parsing
# at all.  "L1" in one model and "01-FIRST FLOOR" in another at the same
# finished floor level breaks stacking silently: nothing in either model looks
# wrong on its own, and the fault only appears once the set is federated.
# ----------------------------------------------------------------------------

def norm_storey(name):
    """The form two storey names are compared in: case and spacing only.

    Deliberately shallow.  Equating 'L1' with '01-FIRST FLOOR' needs a naming
    convention this tool has no way to know, and guessing one would silently
    pass exactly the disagreement the check exists to find.
    """
    return re.sub(r'\s+', ' ', (name or '').strip()).upper()


def level_groups(res, lab, tol_m):
    """Every model's storeys, clustered by the level they sit at.

    Clustering is single-link on the sorted levels: two storeys land in one
    group when they are within the tolerance of each other, which is how the
    1 mm rounding difference between two exports reads as one level.
    """
    rows = []
    for r in res:
        for s in (r.get('spatial') or {}).get('storeys') or ():
            if s['level_m'] is not None:
                rows.append((s['level_m'], lab[r['file']], s))
    rows.sort(key=lambda t: t[0])

    raw = []
    for row in rows:
        if raw and row[0] - raw[-1][-1][0] <= tol_m:
            raw[-1].append(row)
        else:
            raw.append([row])

    out = []
    for g in raw:
        names = []
        for z, l, s in g:
            key = norm_storey(s['name'])
            for n in names:
                if n['key'] == key:
                    n['models'].append(l)
                    n['rows'].append((l, s))
                    break
            else:
                names.append({'key': key, 'name': s['name'], 'models': [l],
                              'rows': [(l, s)]})
        out.append({'z': median([z for z, _, _ in g]),
                    'low': g[0][0], 'high': g[-1][0], 'names': names,
                    'models': [l for _, l, _ in g]})
    return out


def storey_conflicts(groups, datum_m, tol_m=0.05, h_off=None):
    """Where the models disagree about the storeys.

    Two separate faults, because they have different fixes:

      one level, several names   nothing geometric is wrong, but anything
                                 grouping the package by storey - a viewer, a
                                 4D sequence, a BCF issue list - sees two
                                 levels where there is one
      one name, several levels   the models disagree about where a named level
                                 is, so one of them stacks wrong

    The second is graded on how far apart they are.  A structural model
    carries top of concrete where the architectural model carries finished
    floor level, so a slab-thickness offset under one name is a datum
    difference to confirm rather than a mistake to fix.  A difference past
    that is not explainable that way.

    h_off, when given, is each model's own survey height against the package
    median - what G05 grades.  A storey difference that disappears once those
    offsets are taken out is not a storey fault at all: the levels agree and
    the models are hung at different heights, which G05 already reports.
    Naming it twice would send the author to fix the storeys instead.
    """
    split = [g for g in groups if len(g['names']) > 1]
    h_off = h_off or {}

    where = defaultdict(list)
    for g in groups:
        for n in g['names']:
            where[n['key']].append((g, n))
    drift = []
    for key, hits in where.items():
        if len(hits) < 2:
            continue
        zs = [g['z'] for g, _ in hits]
        spread = max(zs) - min(zs)
        levelled = [s['level_m'] - h_off.get(l, 0.0)
                    for _, n in hits for l, s in n['rows']]
        drift.append({'name': hits[0][1]['name'], 'spread_m': spread,
                      'datum': spread <= datum_m,
                      'anchor': max(levelled) - min(levelled) <= tol_m,
                      'at': sorted([(g['z'], ', '.join(n['models']))
                                    for g, n in hits], key=lambda t: t[0])})
    drift.sort(key=lambda d: -d['spread_m'])
    return split, drift


def _anchor_offsets(res, lab):
    """Each model's own survey height against the package median, in metres.

    Storey levels are read in the survey datum, so a model hung half a metre
    high carries every one of its storeys half a metre high.  That is the
    anchor finding (G05), not a storey finding, and these offsets are what
    let the storey check say so instead of repeating it.
    """
    anc = [(lab[r['file']], georef_anchor(r)) for r in res
           if r['site_origin_m'] or r['map_conversion']]
    if not anc:
        return {}
    mid = median([a[2] for _, a in anc])
    return dict((l, a[2] - mid) for l, a in anc)


def level_words(g):
    """'+4.200 m is "K20L-L1" in AR, ME and "01-LEVEL 1" in PI1'."""
    return '%+.3f m is %s' % (g['z'], ' and '.join(
        '"%s" in %s' % (n['name'], ', '.join(n['models'])) for n in g['names']))


def drift_words(d):
    """'"K20L-B1" sits at -7.300 m in AR and -6.800 m in ST'."""
    return '"%s" sits at %s' % (d['name'], ' and '.join(
        '%+.3f m in %s' % (z, who) for z, who in d['at']))


# ----------------------------------------------------------------------------
# Georeferencing
# ----------------------------------------------------------------------------

def map_transform(mc):
    """IfcMapConversion parameters -> function (local x,y,z in project units) -> (E,N,H)."""
    if not mc or mc.get('eastings') is None:
        return None
    ca = mc.get('xaxis_abscissa')
    sa = mc.get('xaxis_ordinate')
    if ca is None and sa is None:
        ca, sa = 1.0, 0.0
    ca = 1.0 if ca is None else ca
    sa = 0.0 if sa is None else sa
    n = math.hypot(ca, sa) or 1.0
    ca, sa = ca / n, sa / n
    s = mc.get('scale')
    s = 1.0 if s is None else s
    e0, n0, h0 = mc['eastings'], mc['northings'], mc.get('height') or 0.0

    def f(p):
        x, y, z = p[0], p[1], p[2]
        return (e0 + s * (x * ca - y * sa),
                n0 + s * (x * sa + y * ca),
                h0 + s * z)
    return f


def expected_scale(unit_to_mm, map_unit_to_mm):
    """
    IfcMapConversion.Scale converts project length units into CRS map units,
    so its correct value follows from the two units alone: a millimetre model
    on a metre CRS must carry 0.001, a metre model 1.0.  Comparing raw Scale
    values ACROSS models is therefore meaningless whenever their length units
    differ - each is checked against its own expected value instead.
    """
    if not unit_to_mm or not map_unit_to_mm:
        return None
    return unit_to_mm / map_unit_to_mm


# Level of georeferencing, after Clemen & Goerne (LoGeoRef).  Each level is a
# different IFC mechanism; only 50 is a complete, unambiguous declaration.
LOGEOREF = {
    0:  'none',
    10: 'postal address only',
    20: 'IfcSite latitude/longitude',
    30: 'IfcSite placement carries the survey offset',
    40: 'model context WorldCoordinateSystem / TrueNorth',
    50: 'IfcMapConversion + IfcProjectedCRS',
}


def georef_anchor(r):
    """
    Where this model's IfcSite origin lands in map coordinates, in metres.

    This is the number every model in a package must agree on, whichever
    mechanism carries it.  Comparing IfcMapConversion values alone is blind
    when the offset lives in the IfcSite placement instead - which is exactly
    the case for a Revit export made without shared coordinates.
    """
    o = r['site_origin_m'] or [0.0, 0.0, 0.0]
    mc = r['map_conversion']
    if not mc or mc.get('eastings') is None:
        return tuple(o)
    ca = mc.get('xaxis_abscissa')
    sa = mc.get('xaxis_ordinate')
    if ca is None and sa is None:
        ca, sa = 1.0, 0.0
    ca = 1.0 if ca is None else ca
    sa = 0.0 if sa is None else sa
    n = math.hypot(ca, sa) or 1.0
    ca, sa = ca / n, sa / n
    mu = (r['map_unit_to_mm'] or 1000.0) / 1000.0      # map unit -> metres
    e0 = (mc['eastings'] or 0.0) * mu
    n0 = (mc['northings'] or 0.0) * mu
    h0 = (mc.get('height') or 0.0) * mu
    return (e0 + o[0] * ca - o[1] * sa,
            n0 + o[0] * sa + o[1] * ca,
            h0 + o[2])


def georef_level(r):
    """Highest georeferencing mechanism actually populated in this model."""
    if r['map_conversion_status'] == 'set' and r['projected_crs']:
        return 50
    if r['wcs_offset'] or (r['true_north_deg'] not in (None, 0.0)):
        lvl = 40
    else:
        lvl = 0
    o = r['site_origin_m']
    if o and max(abs(o[0]), abs(o[1])) > 1.0:
        lvl = max(lvl, 30)
    if lvl >= 30:
        return lvl
    if r['ref_lat'] is not None or r['ref_long'] is not None:
        return 20
    if r['has_address']:
        return 10
    return lvl


def georef_advice(res, lab):
    """
    Plain-language remediation aimed at the model author.

    The recurring misconception is that naming a CRS georeferences a model.
    It does not: IfcProjectedCRS says which map the coordinates belong to,
    IfcMapConversion says where on that map the project origin sits.  One is
    the destination, the other is the journey.
    """
    out = []
    below = [r for r in res if georef_level(r) < 50]
    if not below:
        return out
    lvls = sorted(set(georef_level(r) for r in below))
    out.append('Why this matters')
    out.append('  IfcProjectedCRS names the map (here %s). It does NOT say where'
               % (', '.join(sorted(set(str(r['projected_crs']) for r in below
                                       if r['projected_crs']))) or 'none declared'))
    out.append('  the model sits on that map. That is IfcMapConversion: Eastings,')
    out.append('  Northings, OrthogonalHeight, the rotation to grid north, and the')
    out.append('  unit Scale. A CRS without a MapConversion is a postcode district')
    out.append('  with no street address - you know the map, not the position.')
    out.append('')
    out.append('  Levels found in this package (LoGeoRef):')
    for lv in lvls:
        who = ', '.join(lab[r['file']] for r in below if georef_level(r) == lv)
        out.append('    %-3d %-46s %s' % (lv, LOGEOREF[lv], who))
    out.append('    50  %-46s %s' % (LOGEOREF[50],
               ', '.join(lab[r['file']] for r in res if georef_level(r) == 50) or '(none)'))
    out.append('')
    if any(georef_level(r) == 30 for r in below):
        out.append('  Level 30 works only by accident. The survey offset is baked into')
        out.append('  the IfcSite placement, so a reader that correctly applies the')
        out.append('  zero MapConversion still lands in the right place - but nothing')
        out.append('  in the file distinguishes "identity because already positioned"')
        out.append('  from "identity because nobody filled it in", and any tool that')
        out.append('  re-bases the site placement silently loses the georeference.')
        out.append('')
    stuck = [r for r in below if not can_map_convert(r['schema'])]
    if stuck:
        out.append('  %s on a schema that predates IfcMapConversion:'
                   % plural(len(stuck), 'model'))
        for r in stuck:
            out.append('    %-8s %s' % (lab[r['file']], r['schema']))
        out.append('  No export setting georeferences these. IfcMapConversion and')
        out.append('  IfcProjectedCRS arrive with IFC4, so the steps below only')
        out.append('  take effect once the export target is IFC4 or later. Change')
        out.append('  the schema first, then georeference.')
        out.append('')
    out.append('How to fix it (Revit, which produced these files)')
    out.append('  1. Manage > Coordinates > Specify Coordinates at Point - give the')
    out.append('     survey point its true E/N/elevation.')
    out.append('  2. Manage > Position > Rotate True North - set the angle between')
    out.append('     project north and grid north.')
    out.append('  3. Export IFC > Modify Setup > Site tab: set Coordinate Base to')
    out.append('     "Project Base Point" or "Survey Point" (not Internal), and enter')
    out.append('     the EPSG code so the exporter writes IfcProjectedCRS.')
    out.append('  4. Re-export and re-run this audit: MapConversion should then carry')
    out.append('     non-zero Eastings/Northings/Height.')
    out.append('  Keep the model built near its own internal origin. Modelling at full')
    out.append('  survey coordinates costs geometric precision and is not needed once')
    out.append('  MapConversion carries the offset.')
    out.append('')
    out.append('  Agree one survey point, one CRS and one height datum across every')
    out.append('  discipline before re-export, and have each author use the same')
    out.append('  shared-coordinates file.')
    return out


def mapconv_status(mc, rot, local_centre_m):
    """
    Classify an IfcMapConversion as 'absent', 'placeholder' or 'set'.

    An all-zero conversion with no rotation is an identity transform: the
    exporter wrote the entity but never filled it in.  That is not a
    georeference, and it must not be allowed to read as one just because
    several models agree on the same zeros.  Which remedy applies depends on
    whether the model geometry already carries real-world coordinates, so the
    two cases are named separately.
    """
    if not mc:
        return 'absent', 'model is not georeferenced'
    vals = [mc.get('eastings') or 0.0, mc.get('northings') or 0.0,
            mc.get('height') or 0.0]
    if any(abs(v) > 1e-6 for v in vals) or abs(rot or 0.0) > 1e-9:
        return 'set', ''
    # identity transform - is the model drawn on world coordinates instead?
    big = local_centre_m and max(abs(local_centre_m[0]), abs(local_centre_m[1])) > 1000.0
    if big:
        return 'placeholder', ('all zeros: placeholder, not a georeference - '
                               'coordinates are carried in the model geometry')
    return 'placeholder', 'all zeros: placeholder, model is not georeferenced'


def grid_rotation(mc):
    if not mc:
        return None
    ca = mc.get('xaxis_abscissa')
    sa = mc.get('xaxis_ordinate')
    if ca is None and sa is None:
        return 0.0
    return round(math.degrees(math.atan2(sa or 0.0, ca if ca is not None else 1.0)), 6)


# ----------------------------------------------------------------------------
# Per-file audit
# ----------------------------------------------------------------------------

def audit_file(path, opt):
    m = Model(path)
    u = m.to_mm or 1.0                       # project unit -> mm
    unit_assumed = m.to_mm is None
    me = lambda v: v * u / 1000.0            # project units -> metres

    # -- element extents ----------------------------------------------------
    elems = []
    for e in m.elements:
        M = m.placement(e.place_id)
        local = m.body_bb(e.shape_id)
        if local is not None:
            e.bbox = bb_transform(local, M)
            e.source = 'body'
        if e.bbox is None:
            if e.place_id is None:
                continue
            t = M[1]
            e.bbox = (t[0], t[1], t[2], t[0], t[1], t[2])
            e.source = 'placement'
        elems.append(e)

    n_body = sum(1 for e in elems if e.source == 'body')

    # -- duplicates ---------------------------------------------------------
    tol = opt.dup_tol / u                    # mm -> project units
    # only elements with a real extent: a placement origin is a point, and a
    # pair of points could never be graded above PROBABLE anyway
    solid = [e for e in elems if e.source == 'body']
    n_dup_skipped = len(elems) - len(solid)
    dup_groups, _ = find_duplicates(m, solid, tol, opt.dup_iou, opt.probable_iou)
    dup_ids = {i for g in dup_groups for i in g['ids']}

    dup_guid = {g: c for g, c in m.guid_count.items() if c > 1 and g}
    dup_guid_list = [(g, c, m.guid_detail[g]) for g, c in
                     sorted(dup_guid.items(), key=lambda x: -x[1])]

    # -- interferences (opt-in) --------------------------------------------
    inter, n_oversize = ([], 0)
    if opt.clash:
        inter, n_oversize = find_interferences(m, elems, opt.clash_frac, dup_ids)

    # -- envelope, centre, floating ----------------------------------------
    centres = [bb_centre(e.bbox) for e in elems]
    envelope = None
    for e in elems:
        envelope = bb_union(envelope, e.bbox)
    floating, centre, float_thr = find_floating(elems, centres, u, opt)
    footprint = None
    if envelope:
        footprint = [round(me(envelope[3] - envelope[0]), 1),
                     round(me(envelope[4] - envelope[1]), 1),
                     round(me(envelope[5] - envelope[2]), 1)]

    # -- georeferencing -----------------------------------------------------
    f = map_transform(m.map_conv)
    world_centre = [round(v, 3) for v in f(centre)] if (f and centre) else None
    world_origin = [round(v, 3) for v in f((0., 0., 0.))] if f else None
    world_env = None
    if f and envelope:
        pts = [f((envelope[0 + i * 3], envelope[1 + j * 3], envelope[2 + k * 3]))
               for i in (0, 1) for j in (0, 1) for k in (0, 1)]
        world_env = [round(v, 3) for v in bb_points(pts)]

    # -- IfcClass / PredefinedType ------------------------------------------
    cls = classify_elements(m, elems)
    bad_types = audit_type_objects(m)

    # -- spatial structure --------------------------------------------------
    spatial = audit_spatial(m, elems, u)

    site = m.site[0] if m.site else (None, None, None, '')
    return {
        'file': m.name, 'schema': m.schema,
        'view_definition': m.view_def, 'exchange_requirement': m.exchange_req,
        'coordinate_reference': m.coord_ref, 'authoring_tool': m.authoring_tool,
        'preprocessor': m.preprocessor, 'export_date': m.export_date,
        'view_status': list(view_status(m.view_def, m.schema, m.authoring_tool)),
        'classification': cls,
        'spatial': spatial,
        'bad_type_objects': bad_types[:2000],
        'n_bad_type_objects': len(bad_types),
        'n_type_objects': len(m.type_ids),
        'length_unit': m.unit_name, 'unit_to_mm': m.to_mm, 'unit_assumed_mm': unit_assumed,
        'true_north_deg': m.true_north, 'wcs_offset': m.wcs_offset,
        'ref_lat': site[0], 'ref_long': site[1], 'ref_elev': site[2],
        'n_sites': len(m.site), 'n_projects': m.n_projects,
        'projected_crs': m.crs, 'map_conversion': m.map_conv,
        'map_unit': m.map_unit_name, 'map_unit_to_mm': m.map_to_mm,
        'grid_rotation_deg': grid_rotation(m.map_conv),
        'site_origin_m': [round(me(v), 4) for v in m.site_origin] if m.site_origin else None,
        'has_address': m.has_address,
        'map_conversion_status': mapconv_status(
            m.map_conv, grid_rotation(m.map_conv),
            [round(me(v), 2) for v in centre] if centre else None)[0],
        'local_centre_m': [round(me(v), 2) for v in centre] if centre else None,
        'world_centre_ENH': world_centre, 'world_origin_ENH': world_origin,
        'world_envelope_ENH': world_env,
        'footprint_m': footprint,
        'float_thresholds_m': float_thr,
        'n_elements': len(elems), 'n_with_body_geometry': n_body,
        'n_dup_skipped': n_dup_skipped,
        'n_aggregate_containers': m.n_containers,
        'unhandled_geometry': dict(m.unhandled.most_common(8)),
        'dup_guid_groups': len(dup_guid),
        'dup_guid_extra': sum(c - 1 for c in dup_guid.values()),
        'dup_guid_detail': dup_guid_list[:20],
        'duplicates': dup_groups,
        'n_duplicate_groups': sum(1 for g in dup_groups if g['verdict'] == 'DUPLICATE'),
        'n_duplicate_extra': sum(g['count'] - 1 for g in dup_groups if g['verdict'] == 'DUPLICATE'),
        'n_probable_groups': sum(1 for g in dup_groups if g['verdict'] == 'PROBABLE'),
        'interferences': inter[:5000], 'n_interferences': len(inter),
        'n_interference_skipped': n_oversize,
        'n_floating': len(floating), 'floating': floating[:40],
        'n_detached': sum(1 for f in floating if f['grade'] == FIX),
        'n_outlying': sum(1 for f in floating if f['grade'] == REVIEW),
    }


# ----------------------------------------------------------------------------
# Report
# ----------------------------------------------------------------------------

def fmt(v):
    return '-' if v is None else v


def f3(v):
    return '-' if v is None else ('%.3f' % v)


def brief(pairs, cap=6):
    """'AR (1), DR (1), ... and 4 more' - keep findings to one readable line."""
    shown = ', '.join('%s (%d)' % p for p in pairs[:cap])
    return shown + ('' if len(pairs) <= cap else ' and %d more' % (len(pairs) - cap))


def wrap(text, width, indent):
    """Fold a finding onto continuation lines rather than running off screen."""
    words = text.split()
    lines = []
    cur = ''
    for wd in words:
        if cur and len(cur) + 1 + len(wd) > width:
            lines.append(cur)
            cur = wd
        else:
            cur = (cur + ' ' + wd).strip()
    if cur:
        lines.append(cur)
    return (chr(10) + ' ' * indent).join(lines)


def plural(n, word, ending='s'):
    return '%d %s%s' % (n, word, '' if n == 1 else ending)


# Readable spellings for the IFC classes that actually show up in findings.
# Anything unlisted falls back to Ifc + capitalised remainder, which is still
# easier to scan than a wall of upper case.
IFC_NAMES = {}
for _n in ('Wall', 'WallStandardCase', 'Slab', 'Beam', 'Column', 'Footing', 'Pile',
           'Member', 'Plate', 'Door', 'Window', 'Stair', 'StairFlight', 'Ramp',
           'RampFlight', 'Railing', 'Roof', 'Covering', 'CurtainWall', 'Space',
           'Furniture', 'FurnishingElement', 'BuildingElementProxy', 'Chimney',
           'Shading Device', 'ShadingDevice', 'DiscreteAccessory', 'MechanicalFastener',
           'ReinforcingBar', 'ReinforcingMesh', 'Tendon', 'PipeSegment', 'PipeFitting',
           'DuctSegment', 'DuctFitting', 'DuctSilencer', 'Valve', 'Pump', 'Tank',
           'Boiler', 'Chiller', 'AirTerminal', 'AirTerminalBox', 'CableCarrierSegment',
           'CableCarrierFitting', 'CableSegment', 'CableFitting', 'JunctionBox',
           'LightFixture', 'Outlet', 'SwitchingDevice', 'ElectricAppliance',
           'ElectricDistributionBoard', 'ElectricGenerator', 'ElectricMotor',
           'DistributionElement', 'DistributionControlElement', 'FlowInstrument',
           'SanitaryTerminal', 'FireSuppressionTerminal', 'Sensor', 'Actuator',
           'BuildingElementPart', 'Opening Element', 'OpeningElement', 'Transformer',
           'UnitaryEquipment', 'Fan', 'Filter', 'HeatExchanger', 'Humidifier',
           'CoolingTower', 'Compressor', 'Condenser', 'Evaporator', 'Damper',
           'ProtectiveDevice', 'MotorConnection', 'Controller', 'Alarm', 'Interceptor',
           'Stack Terminal', 'StackTerminal', 'WasteTerminal', 'Grid', 'Annotation',
           # generic supertypes an IFC2x3 MEP export lands on
           'FlowSegment', 'FlowFitting', 'FlowTerminal', 'FlowController',
           'FlowMovingDevice', 'FlowStorageDevice', 'FlowTreatmentDevice',
           'EnergyConversionDevice', 'DistributionFlowElement',
           'DistributionChamberElement', 'ElementAssembly', 'ElementComponent',
           # the rest of the IFC4 / IFC4x3 classes a building model reaches for
           'FlowMeter', 'CommunicationsAppliance', 'AudioVisualAppliance',
           'MedicalDevice', 'ElectricFlowStorageDevice', 'SolarDevice',
           'SpaceHeater', 'WasteTerminalType', 'BuiltElement', 'BuildingSystem',
           'DistributionSystem', 'DistributionPort', 'DistributionBoard',
           'ElectricTimeControl', 'AirToAirHeatRecovery', 'BurnerType',
           'CoilType', 'TubeBundle', 'VibrationIsolator', 'Coil', 'Burner',
           'CivilElement', 'GeographicElement', 'TransportElement',
           'SystemFurnitureElement', 'Furniture', 'CurtainWall',
           'BuildingElementProxyType', 'Pile', 'Footing', 'StairFlight',
           'RampFlight', 'Wall', 'Roof', 'Ceiling',
           # the spatial containers, which findings now name as well
           'Project', 'Site', 'Building', 'BuildingStorey', 'SpatialZone',
           'Zone', 'SpatialStructureElement', 'SpatialElement'):
    IFC_NAMES['IFC' + _n.replace(' ', '').upper()] = 'Ifc' + _n.replace(' ', '')


def ifc_name(cls):
    """IFCPIPEFITTING -> IfcPipeFitting (all upper case is hard to skim)."""
    if not cls:
        return '-'
    known = IFC_NAMES.get(cls.upper())
    if known:
        return known
    # IFCVALVETYPE -> IfcValveType, off the occurrence class already listed
    if cls.upper().endswith('TYPE'):
        base = IFC_NAMES.get(cls.upper()[:-4])
        if base:
            return base + 'Type'
    if cls.upper().startswith('IFC'):
        return 'Ifc' + cls[3:].capitalize()
    return cls.capitalize()


def model_labels(res):
    """
    Short handle per model, so long shared file-name prefixes are printed once.

    Derived by stripping the prefix and suffix every file name shares, then
    keeping the first field of what remains - which for ISO 19650 style names
    lands on the discipline code (AR, ST, PI...).  Collisions get a number.
    Falls back to M1, M2... when the names have no distinguishing stem.
    """
    names = [r['file'] for r in res]
    if len(names) == 1:
        return {names[0]: 'M1'}
    pre = os.path.commonprefix(names)
    suf = os.path.commonprefix([n[::-1] for n in names])[::-1]
    out = {}
    used = Counter()
    for n in names:
        stem = n[len(pre):len(n) - len(suf)] if len(pre) + len(suf) < len(n) else ''
        lab = re.split(r'[-_. ]', stem)[0][:6].upper() if stem else ''
        if not lab or not re.match(r'^[A-Z0-9]+$', lab):
            lab = 'M%d' % (len(out) + 1)
        out[n] = lab
    for n in names:                       # disambiguate repeated labels
        used[out[n]] += 1
    seen = Counter()
    for n in names:
        lab = out[n]
        if used[lab] > 1:
            seen[lab] += 1
            out[n] = '%s%d' % (lab, seen[lab])
    return out


def overlap_words(ev):
    """'IoU 0.87' -> '87% overlap'; keep anything else as written."""
    m = re.match(r'IoU\s+([0-9.]+)$', ev or '')
    if not m:
        return ev
    v = float(m.group(1))
    return 'boxes identical' if v >= 0.995 else '%d%% overlap' % round(v * 100)


def block_runs(groups):
    """
    Collapse duplicate groups that repeat with a constant id offset.

    A block of elements copied in one action produces many pairs whose two ids
    differ by the same amount.  Reporting those as N independent duplicates
    buries the finding; they are one mistake.  Returns (blocks, singles).
    """
    by_key = defaultdict(list)
    for g in groups:
        if g['count'] == 2 and len(g['ids']) == 2:
            by_key[(g['class'], g['type'], g['ids'][1] - g['ids'][0])].append(g)
    claimed = set()
    blocks = []
    for (cls, typ, off), gs in by_key.items():
        if len(gs) < 3:
            continue
        for g in gs:
            claimed.add(id(g))
        blocks.append({'class': cls, 'type': typ, 'offset': off, 'groups': gs,
                       'verdict': 'DUPLICATE' if any(x['verdict'] == 'DUPLICATE'
                                                     for x in gs) else 'PROBABLE'})
    blocks.sort(key=lambda b: -len(b['groups']))
    singles = [g for g in groups if id(g) not in claimed]
    return blocks, singles


def centre_spread(res):
    """Largest distance between model centres, and the model furthest out."""
    pts = [(r, r['world_centre_ENH'] or r['local_centre_m']) for r in res]
    pts = [(r, p) for r, p in pts if p]
    if len(pts) < 2:
        return None, None, None
    worst = 0.0
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            d = math.hypot(pts[i][1][0] - pts[j][1][0], pts[i][1][1] - pts[j][1][1])
            worst = max(worst, d)
    mx = median([p[0] for _, p in pts])
    my = median([p[1] for _, p in pts])
    far = max(pts, key=lambda rp: math.hypot(rp[1][0] - mx, rp[1][1] - my))
    return worst, far[0], math.hypot(far[1][0] - mx, far[1][1] - my)


# ----------------------------------------------------------------------------
# Findings
# ----------------------------------------------------------------------------

FIX, REVIEW, PASS = '!', '?', 'ok'

# ----------------------------------------------------------------------------
# Rule registry
#
# Every finding carries a stable id, so it can be cited - in an email, a BEP,
# or a comment back from the design team.  "the audit flagged your
# georeferencing" is not something a design team can file, argue with or close
# out; G02 is.
#
# The rules are the tool.  What a particular client, authority or region asks
# for is NOT: that lives in a profile file, because this tool is run on
# projects in several countries and anything baked in here would be wrong for
# most of them.  See load_profile.
# ----------------------------------------------------------------------------

RULES = (
    # id    area               title
    ('F01', 'Unreadable',      'File readable'),
    ('F02', 'Schema',          'Schema version'),
    ('F03', 'Schema',          'Schema addenda consistency'),
    ('F04', 'Units',           'Length units consistent'),
    ('F05', 'View definition', 'View definition / MVD'),
    ('F06', 'IfcProject',      'IfcProject present'),
    ('F07', 'IfcSite',         'IfcSite present'),
    ('F08', 'IfcSite',         'One IfcSite per model'),
    ('S01', 'Spatial tree',    'Spatial hierarchy rooted'),
    ('S02', 'Storeys',         'Building storeys present'),
    ('S03', 'Storeys',         'Storey agreement across models'),
    ('S04', 'Containment',     'Elements assigned to a storey'),
    ('S05', 'Spaces',          'Rooms modelled as IfcSpace'),
    ('G01', 'CRS',             'Projected CRS declared'),
    ('G02', 'Georeferencing',  'Level of georeferencing'),
    ('G03', 'Georeferencing',  'MapConversion agreement'),
    ('G04', 'Georeferencing',  'MapConversion scale'),
    ('G05', 'Site anchor',     'Site anchor agreement'),
    ('D01', 'GlobalIds',       'GlobalId uniqueness'),
    ('D02', 'Duplicates',      'Duplicate elements'),
    ('D03', 'Probable dups',   'Probable duplicates'),
    ('C01', 'Proxies',         'Generic proxies'),
    ('C02', 'Classification',  'Classification completeness'),
    ('C03', 'Schema rule',     'Type object PredefinedType rule'),
    ('X01', 'Geometry',        'Geometry coverage'),
    ('X02', 'Floating',        'Floating elements'),
    ('X03', 'Interferences',   'Interferences'),
)
RULE = dict((r[0], {'id': r[0], 'area': r[1], 'title': r[2]}) for r in RULES)


# ----------------------------------------------------------------------------
# Submission profiles
#
# A profile is a JSON file, not a table in this source.  Every jurisdiction,
# client and BEP asks for a different schema, a different MVD and a different
# set of named checks, and a tool used across several countries cannot carry
# any one of them as its default without being wrong everywhere else.  A
# profile is therefore project data: keep it beside the project, not here.
#
#   {
#     "name":    "Acme Tower - stage 3 issue",
#     "version": "2026-10",
#     "options": {"expect_schema": "IFC4", "expect_view": "ReferenceView",
#                 "clash": true},
#     "severity_words": {"!": "FAIL", "?": "ALERT", "ok": "PASS"},
#     "checks": [
#       {"id": "A-01", "title": "Models are IFC4 Reference View",
#        "rules": ["F02", "F05"], "cover": "partial",
#        "note": "the declared MVD is read from the file header"}
#     ]
#   }
#
# "options" takes the long form of any command-line option, underscored.
# "checks" is the external checklist the profile answers - a regulator's codes,
# a client's EIR clauses, a BEP's acceptance criteria - mapped onto the rules
# that address each one.  Listing a check with no rules behind it is the point
# of the section rather than an omission: it is how the report says out loud
# which of the asks this run did not examine.
# ----------------------------------------------------------------------------

# Options a profile may set.  A profile states what to check for; it does not
# get to redirect where output goes or which files are read.
PROFILE_OPTIONS = {
    'expect_schema', 'expect_view', 'clash', 'clash_frac', 'dup_tol', 'dup_iou',
    'probable_iou', 'geo_tol', 'min_geometry', 'min_classified', 'float_k',
    'float_detach', 'float_min', 'float_xy', 'float_z', 'max_rows',
    'storey_tol', 'storey_datum',
}

COVER_WORDS = ('covered', 'partial')


def load_profile(path):
    """Read a profile file, and check it says what it claims to say."""
    try:
        with open(path, 'r', encoding='utf-8') as fh:
            prof = json.load(fh)
    except ValueError as e:
        raise ValueError('%s is not valid JSON: %s' % (path, e))
    if not isinstance(prof, dict):
        raise ValueError('%s must contain a JSON object' % path)

    bad = sorted(set(prof.get('options') or {}) - PROFILE_OPTIONS)
    if bad:
        raise ValueError('%s sets %s, which a profile may not set; allowed: %s'
                         % (path, ', '.join(bad), ', '.join(sorted(PROFILE_OPTIONS))))
    words = prof.get('severity_words') or {}
    if words and sorted(words) != sorted((FIX, REVIEW, PASS)):
        raise ValueError('%s severity_words must name exactly these three: %s'
                         % (path, ', '.join(repr(w) for w in (FIX, REVIEW, PASS))))

    checks = []
    for i, c in enumerate(prof.get('checks') or ()):
        ids = tuple(c.get('rules') or ())
        unknown = [r for r in ids if r not in RULE]
        if unknown:
            raise ValueError('%s check %s names unknown %s: %s'
                             % (path, c.get('id', i), plural(len(unknown), 'rule'),
                                ', '.join(unknown)))
        # A profile may not claim coverage it has no rule for.  Saying which
        # asks went unexamined is the whole reason the section exists, so that
        # one statement stays the tool's to make rather than the file's.
        cover = c.get('cover') if ids else 'not yet'
        if cover not in COVER_WORDS:
            cover = 'partial' if ids else 'not yet'
        checks.append({'id': str(c.get('id', '?')), 'title': c.get('title', ''),
                       'rules': ids, 'cover': cover, 'note': c.get('note', '')})
    prof['checks'] = checks
    prof.setdefault('name', os.path.basename(path))
    return prof


def apply_profile(opt):
    """Let the profile fill in anything the caller did not state themselves."""
    if not opt.profile:
        opt.profile_data = None
        return
    prof = load_profile(opt.profile)
    for k, v in (prof.get('options') or {}).items():
        if k not in opt.explicit:          # an explicit flag always wins
            setattr(opt, k, v)
    SEV_WORD.update(prof.get('severity_words') or {})
    opt.profile_data = prof


def rule_checks(prof):
    """rule id -> the ids of the profile checks it contributes to."""
    out = defaultdict(list)
    for c in (prof or {}).get('checks') or ():
        for r in c['rules']:
            out[r].append(c['id'])
    return out


def print_rules():
    """The rule table, so it can be read without running anything."""
    print('')
    print(' ifc_audit rules')
    print('')
    print(' %-6s %-17s %s' % ('rule', 'area', 'title'))
    for rid, area, title in RULES:
        print(' %-6s %-17s %s' % (rid, area, title))
    print('')
    print(' These are the checks the tool performs.  To report them against an')
    print(' external checklist - a regulator, a client EIR, a BEP - write a')
    print(' profile file mapping that checklist onto these ids and pass it with')
    print(' --profile.  The format is in the header of this script.')
    print('')



def collect_findings(res, opt, lab):
    """Everything the reader must decide on, worst first."""
    f = []
    n = len(res)

    def add(sev, rid, text):
        r = RULE[rid]
        f.append({'sev': sev, 'id': rid, 'area': r['area'],
                  'title': r['title'], 'text': text})

    # a model that could not be read is not a model that passed
    for name, why in getattr(opt, 'skipped', ()):
        add(FIX, 'F01', '%s was not audited: %s' % (name, why))

    # --- the two roots of the spatial hierarchy -----------------------------
    # Presence, which is all these two ask.  Whether IfcProject really is the
    # apex with IfcSite below it is S01, which walks the IfcRelAggregates
    # chain; keeping the two apart matters because a model can hold both
    # entities and still have them hanging off nothing.
    #
    # None and too many are different faults with different fixes, so they are
    # raised independently: a model with two is still named when another model
    # in the same package has none.
    no_proj = [lab[r['file']] for r in res if not r['n_projects']]
    many_proj = ['%s (%d)' % (lab[r['file']], r['n_projects'])
                 for r in res if r['n_projects'] > 1]
    if no_proj:
        add(FIX, 'F06', 'no IfcProject in %s - IfcProject is the root every '
            'other entity hangs from, and a file without one carries no units, '
            'no representation context and no spatial hierarchy, so a receiving '
            'system has nothing to open it against' % ', '.join(no_proj))
    if many_proj:
        add(FIX, 'F06', 'more than one IfcProject in %s - IFC allows exactly '
            'one, and which one a reader picks up decides the units and the '
            'representation context it reads the whole file with'
            % ', '.join(many_proj))
    if not no_proj and not many_proj:
        add(PASS, 'F06', 'one IfcProject in each of the %d models' % n)

    no_site = [lab[r['file']] for r in res if not r['n_sites']]
    if no_site:
        add(FIX, 'F07', 'no IfcSite in %s - without one the model has nowhere '
            'to carry a latitude, longitude or address, and nothing states '
            'where on the earth it sits' % ', '.join(no_site))
    else:
        add(PASS, 'F07', 'IfcSite present in each of the %d models' % n)

    multi_site = ['%s (%d)' % (lab[r['file']], r['n_sites'])
                  for r in res if r['n_sites'] > 1]
    if multi_site:
        add(REVIEW, 'F08', 'more than one IfcSite in %s - legal, but the '
            'georeferencing below reads the first one, and a federated package '
            'is only aligned if every model agrees on which site that is'
            % ', '.join(multi_site))

    # --- the spatial tree ---------------------------------------------------
    broken = [(lab[r['file']], r['spatial']['hierarchy']) for r in res
              if not r['spatial']['hierarchy']['ok']]
    if broken:
        bits = []
        for l, h in broken[:3]:
            # one example per model, with a count rather than a page of them;
            # the SPATIAL STRUCTURE section lists every one
            rest = ('' if len(h['problems']) < 2
                    else ' (and %d more in that model)' % (len(h['problems']) - 1))
            bits.append('%s - %s%s' % (l, h['problems'][0], rest))
        more = ('' if len(broken) <= 3
                else '; and %s' % plural(len(broken) - 3, 'further model'))
        add(FIX, 'S01', 'the spatial hierarchy is not rooted in %s: %s%s - a '
            'receiving system walks IfcProject > IfcSite > IfcBuilding > '
            'IfcBuildingStorey to decide what belongs to what, and anything '
            'off that chain is invisible to it however complete the entity '
            'itself looks' % (plural(len(broken), 'model'),
                              '; '.join(bits), more))
    else:
        add(PASS, 'S01', 'every IfcSite, IfcBuilding, IfcBuildingStorey and '
            'IfcSpace in the %d models hangs off the one above it, with '
            'IfcProject at the apex' % n)

    # --- are there storeys to hold anything? --------------------------------
    with_st = [lab[r['file']] for r in res if r['spatial']['n_storeys']]
    no_st = [lab[r['file']] for r in res if not r['spatial']['n_storeys']]
    if with_st and no_st:
        add(REVIEW, 'S02', 'no IfcBuildingStorey in %s while the rest of the '
            'package carries storeys - nothing in those models can be filtered '
            'or federated by level alongside the others' % ', '.join(no_st))
    elif not with_st:
        add(REVIEW, 'S02', 'no IfcBuildingStorey in any of the %d models - '
            'expected of an infrastructure package, where there are no '
            'storeys to model, and a gap in a building one, where it means '
            'nothing states what level anything is on' % n)
    else:
        add(PASS, 'S02', '%s across the %d models'
            % (plural(sum(r['spatial']['n_storeys'] for r in res),
                      'building storey'), n))

    # --- do the models agree on the storeys? --------------------------------
    # The single check Phase 2 exists for: two models can each be internally
    # correct and still not stack, and nothing visible in either one says so.
    groups = level_groups(res, lab, opt.storey_tol / 1000.0)
    # each model's own survey height against the package, so a storey
    # difference that is really the model hanging at the wrong height is sent
    # to G05 rather than reported again here
    split, drift = storey_conflicts(groups, opt.storey_datum / 1000.0,
                                    opt.storey_tol / 1000.0,
                                    _anchor_offsets(res, lab))
    if len(with_st) > 1:
        hard = [d for d in drift if not d['datum'] and not d['anchor']]
        soft = [d for d in drift if d['datum'] and not d['anchor']]
        hung = [d for d in drift if d['anchor']]
        if hung:
            add(REVIEW, 'S03', '%s at a different height in different models, '
                'by exactly the amount those models disagree about their own '
                'survey height: %s - the storeys themselves agree, so this is '
                'the anchor finding above and not a second fault; fix the '
                'survey point and these follow'
                % (plural(len(hung), 'level'),
                   '; '.join(drift_words(d) for d in hung[:4])))
        if hard:
            add(FIX, 'S03', 'the models disagree about where a named level is: '
                '%s - one of them stacks wrong, and nothing in either model '
                'looks wrong on its own'
                % '; '.join(drift_words(d) for d in hard[:4]))
        if soft:
            add(REVIEW, 'S03', 'a named level differs between models by less '
                'than %g mm: %s - a structural model carrying top of concrete '
                'against an architectural one carrying finished floor level '
                'reads exactly like this, so confirm the datum rather than '
                'moving anything'
                % (opt.storey_datum, '; '.join(drift_words(d) for d in soft[:4])))
        if split:
            add(REVIEW, 'S03', '%s named differently between models: %s - '
                'anything that groups the package by storey, a federated '
                'viewer or a 4D sequence or a BCF issue list, sees two levels '
                'where there is one'
                % (plural(len(split), 'level'),
                   '; '.join(level_words(g) for g in split[:4])))
        if not drift and not split:
            add(PASS, 'S03', 'all %s agree on name and level across the %s '
                'that carry storeys'
                % (plural(len(groups), 'level'),
                   plural(len(with_st), 'model')))

    # --- is every element on a storey? --------------------------------------
    loose = [(lab[r['file']], r['spatial']['n_loose'])
             for r in res if r['spatial']['n_loose']]
    above = [(lab[r['file']], r['spatial']['n_above_storey'])
             for r in res if r['spatial']['n_above_storey']]
    if loose:
        add(FIX, 'S04', '%s in no spatial structure at all in %s - an element '
            'outside every IfcRelContainedInSpatialStructure belongs to no '
            'storey, so it shows under no level in a receiving system and is '
            'skipped by anything that walks the model by storey'
            % (plural(sum(x[1] for x in loose), 'element'), brief(loose)))
    if above:
        add(REVIEW, 'S04', '%s held by the site, the building or another '
            'container rather than by a storey in %s - correct for external '
            'works and for anything spanning the whole building, worth '
            'confirming for the rest'
            % (plural(sum(x[1] for x in above), 'element'), brief(above)))
    if not loose and not above and any(r['spatial']['n_in_storey'] for r in res):
        add(PASS, 'S04', 'every element is contained in a storey')

    # --- are the rooms modelled? --------------------------------------------
    # Graded on the package, not per model: a structural or piping model with
    # no IfcSpace is right, and eight findings saying so would bury the one
    # that matters.
    with_sp = [(lab[r['file']], r['spatial']['n_spaces'])
               for r in res if r['spatial']['n_spaces']]
    if not with_sp:
        add(REVIEW, 'S05', 'no IfcSpace in any of the %d models - the rooms '
            'are not modelled, so nothing in this package can be checked, '
            'scheduled or counted by room, and area takeoff has nothing to '
            'read' % n)
    else:
        add(PASS, 'S05', '%s in %s'
            % (plural(sum(x[1] for x in with_sp), 'space'), brief(with_sp)))
    outside = [(lab[r['file']], r['spatial']['n_spaces_outside_storey'])
               for r in res if r['spatial']['n_spaces_outside_storey']]
    if outside:
        add(REVIEW, 'S05', '%s on no storey in %s - a space outside the storey '
            'it belongs to is not counted in that storey\'s area'
            % (plural(sum(x[1] for x in outside), 'space'), brief(outside)))

    # --- schema: the one that decides whether the package federates at all ---
    by_s = defaultdict(list)
    for r in res:
        by_s[r['schema']].append(lab[r['file']])
    schemas = sorted(by_s)
    if opt.expect_schema:
        target = opt.expect_schema.upper()
    else:
        # no stated target: the majority schema is what the package is trying
        # to be, and ties break towards the later schema
        target = max(schemas, key=lambda s: (len(by_s[s]), s))
    tfam = schema_family(target)
    odd = [(s, by_s[s]) for s in schemas if schema_family(s) != tfam]

    mixed_schema = bool(odd)
    if odd:
        stranded = [l for s, ls in odd if not can_map_convert(s) for l in ls]
        note = ''
        if stranded and can_map_convert(target):
            note = ('; %s cannot be georeferenced at all until re-exported - '
                    'IfcMapConversion and IfcProjectedCRS do not exist before '
                    'IFC4, so no export setting will reach LoGeoRef 50'
                    % ', '.join(stranded))
        who = '; '.join('%s %s %s' % (', '.join(ls),
                                      'is' if len(ls) == 1 else 'are', s)
                        for s, ls in odd)
        if len(odd) == len(schemas):
            # nothing is on target - the package is consistent, just not with
            # the schema it was asked for, so the federation wording is wrong
            add(FIX, 'F02', '%s was required but %s%s' % (target, who, note))
        else:
            add(FIX, 'F02',
                'the package is %s but %s - a federated set read against two '
                'schemas gets different entity classes, property sets and '
                'georeferencing per model%s' % (target, who, note))
    elif len(schemas) > 1:
        add(REVIEW, 'F03', 'same schema, mixed addenda: ' + '; '.join(
            '%s in %s' % (s, ', '.join(by_s[s])) for s in schemas))
    elif opt.expect_schema and schema_family(schemas[0]) != tfam:
        add(FIX, 'F02', 'all models are %s, but %s was required'
            % (schemas[0], opt.expect_schema))
    else:
        add(PASS, 'F02', '%s throughout' % schemas[0])

    units = sorted(set(str(r['length_unit']) for r in res))
    if len(units) > 1:
        by_u = defaultdict(list)
        for r in res:
            by_u[str(r['length_unit'])].append(lab[r['file']])
        add(FIX, 'F04', 'mixed: ' + '; '.join(
            '%s in %s' % (u, ', '.join(by_u[u])) for u in units))
    else:
        add(PASS, 'F04', '%s throughout' % units[0])

    named = sorted(set(r['projected_crs'] for r in res if r['projected_crs']))
    blank = [lab[r['file']] for r in res if not r['projected_crs']]
    pre4 = {lab[r['file']] for r in res if not can_map_convert(r['schema'])}
    if len(named) > 1:
        add(FIX, 'G01', 'mixed: ' + ', '.join(named))
    elif not named:
        add(REVIEW, 'G01', 'no IfcProjectedCRS declared in any model')
    elif not blank:
        add(PASS, 'G01', '%s throughout' % named[0])
    elif set(blank) <= pre4:
        # not a disagreement about the CRS - those models have nowhere to put
        # one, which the schema finding already covers
        add(REVIEW, 'G01', '%s wherever the schema allows one; %s cannot carry '
            'an IfcProjectedCRS at all' % (named[0], ', '.join(blank)))
    else:
        add(FIX, 'G01', '%s in some models, none in %s'
            % (named[0], ', '.join(blank)))

    # --- model view definition ---
    rank = {FIX: 0, REVIEW: 1, PASS: 2}
    views = sorted(set(r['view_definition'] or '(none declared)' for r in res))
    if len(views) > 1 and not mixed_schema:
        # when the schemas differ this is a restatement of that, because the
        # exporter picks the string from the schema
        add(FIX, 'F05', 'mixed: ' + ', '.join(views))
    if opt.expect_view:
        want = split_view(opt.expect_view)[0]
        off = [r for r in res
               if split_view(r['view_definition'] or '')[0] != want]
        # A header the exporter writes from the schema is not evidence of the
        # setup used - v3 observed Revit writing CoordinationView into a file
        # exported with the IFC4x3 Reference View setup.  Those models cannot
        # be said to have the wrong MVD, only to be unable to prove the right
        # one, so they are graded apart from a header that really does differ.
        mute = [lab[r['file']] for r in off
                if exporter_artefact(split_view(r['view_definition'] or '')[0],
                                     schema_family(r['schema']),
                                     r['authoring_tool'])]
        hard = [lab[r['file']] for r in off if lab[r['file']] not in mute]
        if hard:
            add(FIX, 'F05', '%s required but not declared by %s - the header '
                'names a different MVD, so anything reading it is told the '
                'wrong one' % (opt.expect_view, ', '.join(hard)))
        if mute:
            add(REVIEW, 'F05', '%s cannot be confirmed as %s: the exporter '
                'writes that header string from the schema whatever view setup '
                'was chosen, so check the export setup itself and state the '
                'intended MVD to the receiving side, because the file will not'
                % (', '.join(mute), opt.expect_view))
    # a model the schema finding already named does not need a second finding
    # restating it as an MVD problem; grade the view on the models that are not
    # already accounted for
    named = {l for s, ls in odd for l in ls}
    cand = [r for r in res if lab[r['file']] not in named] or res
    worst = min(cand, key=lambda r: rank[r['view_status'][0]])
    sev, text = worst['view_status']
    add(sev, 'F05',
        text if (len(cand) == 1 or sev == PASS)
        else '%s: %s' % (lab[worst['file']], text))

    # --- georeferencing ---
    st = {r['file']: r['map_conversion_status'] for r in res}
    lv = {r['file']: georef_level(r) for r in res}
    stuck = [lab[r['file']] for r in res
             if not can_map_convert(r['schema']) and georef_level(r) < 50]
    if stuck:
        add(FIX, 'G02',
            '%s on a pre-IFC4 schema, which has no IfcMapConversion or '
            'IfcProjectedCRS - re-export as IFC4 or later first, because no '
            'georeferencing setting can lift %s to LoGeoRef 50'
            % (plural(len(stuck), 'model'), 'it' if len(stuck) == 1 else 'them'))
    # the remaining grade is about models an export setting can still fix, so a
    # stranded model does not drag the whole package to its own level twice
    fixable = [r for r in res if can_map_convert(r['schema'])]
    worst_lv = min([lv[r['file']] for r in fixable] or [50])
    n_ph = sum(1 for r in fixable if st[r['file']] == 'placeholder')
    n_abs = sum(1 for r in fixable if st[r['file']] == 'absent')
    if not fixable:
        pass
    elif worst_lv >= 50:
        add(PASS, 'G02',
            'IfcMapConversion + IfcProjectedCRS in all %d models'
            % len(fixable))
    elif worst_lv >= 30:
        # positioned, but by a mechanism that carries no declaration of intent
        add(REVIEW, 'G02',
            'positioned by the IfcSite placement, not IfcMapConversion (LoGeoRef %d); '
            '%s left at all zeros - see HOW TO FIX'
            % (worst_lv, plural(n_ph, 'MapConversion') if n_ph else 'no MapConversion'))
    else:
        add(FIX, 'G02',
            'models are not georeferenced (LoGeoRef %d) - %s; see HOW TO FIX'
            % (worst_lv, ', '.join(
                p for p in (plural(n_ph, 'placeholder') if n_ph else '',
                            '%d with no MapConversion' % n_abs if n_abs else '') if p)
               or 'nothing declared'))

    with_mc = [r for r in res if st[r['file']] == 'set']
    if len(with_mc) > 1:
        mu = max((r['map_unit_to_mm'] or 1000.0) for r in with_mc)
        worst = 0.0
        which = ''
        for k, label in (('eastings', 'easting'), ('northings', 'northing'),
                         ('height', 'height')):
            vals = [r['map_conversion'].get(k) for r in with_mc]
            vals = [v for v in vals if v is not None]
            if vals and (max(vals) - min(vals)) > worst:
                worst = max(vals) - min(vals)
                which = label
        if worst > opt.geo_tol / mu:
            add(FIX, 'G03',
                'MapConversion %s differs by %.1f mm across %d models'
                % (which, worst * mu, len(with_mc)))
        else:
            add(PASS, 'G03',
                'all %d MapConversions agree within %.0f mm' % (len(with_mc), opt.geo_tol))

    bad_scale = [lab[r['file']] for r in with_mc
                 if expected_scale(r['unit_to_mm'], r['map_unit_to_mm'])
                 and abs((1.0 if r['map_conversion']['scale'] is None
                          else r['map_conversion']['scale'])
                         - expected_scale(r['unit_to_mm'], r['map_unit_to_mm']))
                 > expected_scale(r['unit_to_mm'], r['map_unit_to_mm']) * 1e-6]
    if bad_scale:
        add(FIX, 'G04',
            'MapConversion Scale wrong for its units in %s' % ', '.join(bad_scale))

    # --- do the models agree on one real-world anchor? ---
    anchors = [(r, georef_anchor(r)) for r in res if r['site_origin_m'] or r['map_conversion']]
    if len(anchors) > 1:
        worst = 0.0
        pair = None
        for i in range(len(anchors)):
            for j in range(i + 1, len(anchors)):
                d = max(abs(anchors[i][1][k] - anchors[j][1][k]) for k in range(3))
                if d > worst:
                    worst = d
                    pair = (anchors[i][0], anchors[j][0])
        if worst > opt.geo_tol / 1000.0:
            mid = [median([a[1][k] for a in anchors]) for k in range(3)]
            far = max(anchors, key=lambda a: max(abs(a[1][k] - mid[k]) for k in range(3)))
            off = [far[1][k] - mid[k] for k in range(3)]
            add(FIX, 'G05',
                'models do not share one survey point: spread %.3f m; %s is off by '
                'E %.3f, N %.3f, H %.3f m'
                % (worst, lab[far[0]['file']], off[0], off[1], off[2]))
        else:
            add(PASS, 'G05',
                'all %d models share one survey point (within %.0f mm)'
                % (len(anchors), opt.geo_tol))

    # --- duplicates ---
    guid = [(lab[r['file']], r['dup_guid_extra']) for r in res if r['dup_guid_extra']]
    if guid:
        add(FIX, 'D01', 'repeated GlobalId (invalid file) in %s'
            % ', '.join('%s (%d)' % g for g in guid))

    dup = [(lab[r['file']], r['n_duplicate_extra']) for r in res if r['n_duplicate_extra']]
    if dup:
        add(FIX, 'D02', '%s in %s'
            % (plural(sum(d[1] for d in dup), 'duplicated element'),
               brief(dup)))
    else:
        add(PASS, 'D02', 'none found')

    prob = [(lab[r['file']], r['n_probable_groups']) for r in res if r['n_probable_groups']]
    if prob:
        add(REVIEW, 'D03', '%s that could not be confirmed in %s'
            % (plural(sum(p[1] for p in prob), 'group'),
               brief(prob)))

    # --- geometry coverage ---
    low = [(lab[r['file']], 100.0 * r['n_with_body_geometry'] / r['n_elements'])
           for r in res if r['n_elements']
           and r['n_with_body_geometry'] < r['n_elements'] * opt.min_geometry]
    if low:
        add(FIX, 'X01', 'geometry unresolved for a large share of %s'
            % ', '.join('%s (%.0f%% resolved)' % l for l in low))

    # --- IfcClass / PredefinedType ---
    prox = [(lab[r['file']], r['classification']['n_proxy'])
            for r in res if r['classification']['n_proxy']]
    if prox:
        add(FIX, 'C01', '%s left as a generic proxy in %s - the exporter '
            'could not map them to an IFC class, so nothing downstream knows '
            'what they are'
            % (plural(sum(p[1] for p in prox), 'element'), brief(prox)))

    cls_pct = [(lab[r['file']],
                100.0 * r['classification']['n_classified'] / r['classification']['n'])
               for r in res if r['classification']['n']]
    low_cls = [c for c in cls_pct if c[1] < opt.min_classified * 100]
    if low_cls:
        add(REVIEW, 'C02',
            'PredefinedType missing or unspecific on %s'
            % ', '.join('%s (%.0f%% classified)' % c for c in low_cls))
    elif not prox and cls_pct:
        add(PASS, 'C02', 'IfcClass and PredefinedType set throughout')

    bt = [(lab[r['file']], r['n_bad_type_objects'])
          for r in res if r['n_bad_type_objects']]
    if bt:
        add(REVIEW, 'C03', '%s with PredefinedType USERDEFINED and no '
            'ElementType in %s - USERDEFINED is allowed, but with ElementType '
            'blank nothing states what the type is; assign a proper '
            'PredefinedType, or name the type in ElementType'
            % (plural(sum(b[1] for b in bt), 'type object'), brief(bt)))

    # --- floating ---
    det = [(lab[r['file']], r['n_detached']) for r in res if r['n_detached']]
    if det:
        add(FIX, 'X02', '%s detached from the model in %s - displaced by '
            'more than %g times the spread of everything else'
            % (plural(sum(x[1] for x in det), 'element'), brief(det),
               opt.float_detach))
    out_ly = [(lab[r['file']], r['n_outlying']) for r in res if r['n_outlying']]
    if out_ly:
        add(REVIEW, 'X02', '%s outside the usual envelope of %s but still '
            'within reach of it - check each against the architectural and '
            'structural envelope before moving anything'
            % (plural(sum(x[1] for x in out_ly), 'element'), brief(out_ly)))
    if not det and not out_ly:
        add(PASS, 'X02', 'none found')

    # --- interferences (informational) ---
    if opt.clash:
        it = [(lab[r['file']], r['n_interferences']) for r in res if r['n_interferences']]
        if it:
            add(REVIEW, 'X03', '%s of overlapping different-type elements in %s'
                % (plural(sum(x[1] for x in it), 'pair'),
                   brief(it)))

    order = {FIX: 0, REVIEW: 1, PASS: 2}
    f.sort(key=lambda x: order[x['sev']])
    return f


# ----------------------------------------------------------------------------
# Report
# ----------------------------------------------------------------------------

def report(res, opt):
    lab = model_labels(res)
    lw = max([len(v) for v in lab.values()] + [len('model')])
    findings = collect_findings(res, opt, lab)
    n_fix = sum(1 for f in findings if f['sev'] == FIX)
    n_rev = sum(1 for f in findings if f['sev'] == REVIEW)

    def rule(ch='='):
        print(ch * SECTION_W)

    # ---------------- verdict ----------------
    rule()
    print(' IFC PACKAGE AUDIT    %s    %s' % (plural(len(res), 'model'),
                                              os.path.commonprefix([r['file'] for r in res])
                                              .rstrip('-_ ') or 'package'))
    rule()
    print('')
    if n_fix or n_rev:
        if getattr(opt, 'profile', None):
            # beside a Model Checker report, in its words
            bits = ['%d %s' % (c, SEV_WORD[sv])
                    for c, sv in ((n_fix, FIX), (n_rev, REVIEW)) if c]
        else:
            bits = []
            if n_fix:
                bits.append(plural(n_fix, 'issue'))
            if n_rev:
                bits.append('%d to review' % n_rev)
        print(' RESULT: %s' % ', '.join(bits))
    else:
        print(' RESULT: no issues found')
    print('')
    for f in findings:
        print(' %-4s %-4s %-15s %s' % ('[%s]' % f['sev'], f['id'], f['area'],
                                       wrap(f['text'], SECTION_W - 27, 27)))

    # ---------------- models ----------------
    section('MODELS')
    fw = max(len(r['file']) for r in res)
    for r in res:
        print(('  %-*s  %-*s  %-9s %-11s %s' % (
            lw, lab[r['file']], fw, r['file'], fmt(r['schema']),
            (fmt(r['length_unit']) or '-') + ('*' if r['unit_assumed_mm'] else ''),
            plural(r['n_elements'], 'element'))).rstrip())
    if any(r['unit_assumed_mm'] for r in res):
        print('  * length unit could not be read; millimetres assumed')

    _export_section(res, opt, lab, lw)
    _spatial_section(res, opt, lab, lw)
    _geo_section(res, opt, lab, lw)
    _dup_section(res, opt, lab, lw)
    if opt.clash:
        _clash_section(res, opt, lab, lw)
    _float_section(res, opt, lab, lw)
    _class_section(res, opt, lab, lw)
    _diag_section(res, opt, lab, lw)
    if getattr(opt, 'profile_data', None):
        _profile_section(opt.profile_data, findings)
    print('')


def _profile_section(prof, findings):
    """The profile's own checklist, against what this run actually did.

    Printed rather than merely recorded, because the gap is the point.  A
    reader who sees a page of rule ids and no gap list will take the run as
    equivalent to whatever external check the profile answers, and it is not
    one: the tool reports what it reports, and the body that set the
    checklist is the one whose result counts.
    """
    checks = prof.get('checks') or ()
    if not checks:
        return
    section('PROFILE COVERAGE')
    name = prof.get('name') or 'profile'
    if prof.get('version'):
        name += '  (%s)' % prof['version']
    print('  %s' % name)
    if prof.get('description'):
        print('%s%s' % ('  ', wrap(prof['description'], SECTION_W - 2, 2)))
    print('')
    # findings arrive worst-first, so the first severity seen for an id is the
    # worst that id reached on this package
    raised = {}
    for f in findings:
        raised.setdefault(f['id'], f['sev'])
    cw = max([len(c['id']) for c in checks] + [5])
    tw = min(max([len(c['title']) for c in checks] + [10]), 44) + 1
    print('  %-*s %-*s %-8s %s' % (cw, 'check', tw, 'what it is', 'here', 'rules'))
    for c in checks:
        marks = ' '.join('%s[%s]' % (i, raised[i]) if i in raised else i
                         for i in c['rules'])
        print('  %-*s %-*s %-8s %s' % (cw, c['id'], tw, c['title'],
                                       c['cover'], marks))
        if c['note']:
            print('%s%s' % (' ' * 14, wrap(c['note'], SECTION_W - 14, 14)))
    print('')
    print('  A rule id with no [!] [?] or [ok] beside it did not run on this')
    print('  package - an empty section is not a pass.')


SECTION_W = 88


def section(title):
    print('')
    print('-' * SECTION_W)
    print(' ' + title)


def support_footer():
    section('SUPPORT AND FEEDBACK')
    print('  Email jerome.cristobal@jacobs.com for any of the following:')
    print('    - Feature requests')
    print('    - Validation changes')
    print('    - Bugs')
    print('')


def _spatial_section(res, opt, lab, lw):
    section('SPATIAL STRUCTURE   '
            '(IfcProject > IfcSite > IfcBuilding > IfcBuildingStorey)')
    print('  %-*s %-6s %-7s %-6s %-20s %s'
          % (lw, 'model', 'rooted', 'storeys', 'spaces', 'on a storey',
             'elsewhere'))
    for r in res:
        sp = r['spatial']
        total = r['n_elements']
        on = sp['n_in_storey']
        rest = []
        if sp['n_above_storey']:
            rest.append('%d on site/building' % sp['n_above_storey'])
        if sp['n_loose']:
            rest.append('%d in nothing [!]' % sp['n_loose'])
        pct = (100.0 * on / total) if total else 0.0
        print(('  %-*s %-6s %-7d %-6d %-20s %s' % (
            lw, lab[r['file']],
            'ok' if sp['hierarchy']['ok'] else 'no[!]',
            sp['n_storeys'], sp['n_spaces'],
            '%d/%d  (%.0f%%)' % (on, total, pct) if total else '-',
            ', '.join(rest) or ('-' if total else ''))).rstrip())

    # -- what is wrong with the tree ----------------------------------------
    if any(r['spatial']['hierarchy']['problems'] for r in res):
        print('')
        print('  NOT ROOTED   aggregated into nothing, or into the wrong thing')
    for r in res:
        probs = r['spatial']['hierarchy']['problems']
        if not probs:
            continue
        print('')
        print('  %s' % lab[r['file']])
        for p in probs[:opt.max_rows]:
            print('    %s' % wrap(p, SECTION_W - 4, 4))
        if len(probs) > opt.max_rows:
            print('    ... and %s more'
                  % plural(len(probs) - opt.max_rows, 'problem'))

    # -- the levels of the package ------------------------------------------
    groups = level_groups(res, lab, opt.storey_tol / 1000.0)
    if groups:
        _levels_block(res, opt, lab, groups)
    elif any(r['spatial']['n_storeys'] for r in res):
        print('')
        print('  No IfcBuildingStorey carries a placement this tool could')
        print('  resolve, so there are no levels to compare.')

    # -- elements that are not on a storey ----------------------------------
    off = [r for r in res
           if r['spatial']['n_loose'] or r['spatial']['n_above_storey']]
    if off:
        print('')
        print('  NOT ON A STOREY')
    for r in off:
        sp = r['spatial']
        print('')
        print('  %s' % lab[r['file']])
        if sp['n_loose']:
            print('    in no spatial structure at all:')
            for cls, c in sp['loose_by_class'][:opt.max_rows]:
                ids = [x['id'] for x in sp['loose'] if x['class'] == cls][:4]
                print('      [!] %-26s %-14s %s'
                      % (ifc_name(cls), plural(c, 'element'),
                         ', '.join('#%d' % i for i in ids)))
        if sp['n_above_storey']:
            print('    held above storey level:')
            for where, c in sp['above_by_container'][:opt.max_rows]:
                print('      [?] %-26s %s' % (where, plural(c, 'element')))


def _levels_block(res, opt, lab, groups):
    """The levels of the package, and where the models disagree about them."""
    split, drift = storey_conflicts(groups, opt.storey_datum / 1000.0,
                                    opt.storey_tol / 1000.0,
                                    _anchor_offsets(res, lab))
    drift_keys = dict((norm_storey(d['name']), d) for d in drift)

    print('')
    print('  LEVELS   the storey placement plus whatever height the model')
    print('           carries in IfcMapConversion - metres in the survey')
    print('           datum, so a model holding the offset in its site')
    print('           placement compares with one holding it in')
    print('           MapConversion.  Storeys within %g mm read as one level.'
          % opt.storey_tol)
    print('')
    nw = min(max([len(n['name']) for g in groups for n in g['names']] + [5]), 26)
    for g in reversed(groups):               # top of the building first
        lead = '%+9.3f' % g['z']
        for n in g['names']:
            mark = ''
            if len(g['names']) > 1:
                mark = ' [?]'
            d = drift_keys.get(n['key'])
            if d:
                mark = ' [?]' if (d['datum'] or d['anchor']) else ' [!]'
            print(('   %-9s  %-*s  %s%s' % (
                lead, nw, n['name'], ', '.join(n['models']), mark)).rstrip())
            lead = ''

    if split or drift:
        print('')
        for d in drift[:opt.max_rows]:
            if d['anchor']:
                why = ('the models hang at different survey heights by this '
                       'same amount, so the storeys agree - see the site '
                       'anchor finding')
            elif d['datum']:
                why = ('a datum difference of %.0f mm; finished floor level '
                       'against top of concrete reads like this'
                       % (d['spread_m'] * 1000.0))
            else:
                why = 'one of them stacks wrong'
            print('   %s %s'
                  % ('[?]' if (d['datum'] or d['anchor']) else '[!]',
                     wrap(drift_words(d) + ' - ' + why, SECTION_W - 7, 7)))
        for g in split[:opt.max_rows]:
            print('   [?] %s' % wrap(
                level_words(g) + ' - one level, more than one name',
                SECTION_W - 7, 7))
        hidden = max(0, len(drift) - opt.max_rows) + max(0, len(split) - opt.max_rows)
        if hidden:
            print('   ... and %s not shown'
                  % plural(hidden, 'further disagreement'))


def _geo_section(res, opt, lab, lw):
    section('GEOREFERENCING')
    print('  %-*s %-12s %-10s %-24s %s' % (lw, 'model', 'CRS', 'ref lat',
          'local centre X/Y (m)', 'world centre E/N (m)'))
    for r in res:
        c = r['local_centre_m']
        wc = r['world_centre_ENH']
        print('  %-*s %-12s %-10s %-24s %s' % (
            lw, lab[r['file']], (fmt(r['projected_crs']) or '-')[:12],
            str(fmt(r['ref_lat']))[:10],
            ('%.2f / %.2f' % (c[0], c[1])) if c else '-',
            ('%.3f / %.3f' % (wc[0], wc[1])) if wc else 'no MapConversion'))

    # State a shared condition once, not once per model.
    groups = defaultdict(list)
    for r in res:
        mc = r['map_conversion']
        key = (r['map_conversion_status'],
               None if not mc else (mc['eastings'], mc['northings'], mc['height'],
                                    r['grid_rotation_deg']))
        groups[key].append(r)
    print('')
    for (status, key), rs in sorted(groups.items(), key=lambda kv: -len(kv[1])):
        who = ', '.join(lab[r['file']] for r in rs[:8])
        if len(rs) > 8:
            who += ' and %d more' % (len(rs) - 8)
        if status == 'absent':
            print('  %s: no IfcMapConversion at all - not georeferenced' % who)
            continue
        e, n, h, rot = key
        line = '  %s: E=%s N=%s H=%s rot=%s deg' % (who, f3(e), f3(n), f3(h), rot)
        if status == 'placeholder':
            print(line + '   [!] PLACEHOLDER')
        else:
            print(line)
    if any(r['map_conversion_status'] == 'placeholder' for r in res):
        print('    An all-zero MapConversion is an identity transform, not a')
        print('    georeference. Models agreeing on those zeros are not thereby')
        print('    proven aligned - here alignment rests on the model coordinates.')

    scales = defaultdict(list)
    for r in res:
        if r['map_conversion']:
            sc = r['map_conversion']['scale']
            scales['1.0 (unset)' if sc is None else str(sc)].append(lab[r['file']])
    if scales:
        print('  Scale: %s' % '; '.join('%s in %s' % (k, ', '.join(v))
                                        for k, v in sorted(scales.items())))
    n_noelev = sum(1 for r in res if r['ref_elev'] in (0.0, None))
    if n_noelev:
        print('  RefElevation unset or zero in %d of %d models' % (n_noelev, len(res)))
    multi = [lab[r['file']] for r in res if r['n_sites'] > 1]
    if multi:
        print('  More than one IfcSite in %s - the rows below read the '
              'first one (F08)' % ', '.join(multi))

    # where each model's own origin actually lands, and whether they agree
    anchors = [(r, georef_anchor(r)) for r in res
               if r['site_origin_m'] or r['map_conversion']]
    if anchors:
        print('')
        print('  Real-world anchor - where each model origin lands (m):')
        mid = [median([a[1][k] for a in anchors]) for k in range(3)]
        for r, a in anchors:
            d = max(abs(a[k] - mid[k]) for k in range(3))
            print('  %-*s E %13.3f  N %14.3f  H %8.3f   LoGeoRef %d%s'
                  % (lw, lab[r['file']], a[0], a[1], a[2], georef_level(r),
                     '   [!] off by %.3f m' % d if d > 0.001 else ''))

    advice = georef_advice(res, lab)
    if advice:
        print('')
        print(' HOW TO FIX THE GEOREFERENCING')
        for line in advice:
            print('  ' + line if line else '')


def _dup_section(res, opt, lab, lw):
    if not any(r['duplicates'] or r['dup_guid_extra'] for r in res):
        return
    section('DUPLICATE ELEMENTS')
    print('  Same IFC class AND same type/family name AND overlapping geometry.')
    print('  Overlap alone is never a duplicate - those are under INTERFERENCES.')
    for r in res:
        if not (r['duplicates'] or r['dup_guid_extra']):
            continue
        print('')
        print('  %s  %s' % (lab[r['file']], r['file']))
        for g, c, det in r['dup_guid_detail'][:opt.max_rows]:
            print('    [!] GlobalId %s reused by %d entities  %s'
                  % (g, c, [d[0] for d in det]))
        if r['dup_guid_groups'] > opt.max_rows:
            print('    ... %d more reused GlobalIds'
                  % (r['dup_guid_groups'] - opt.max_rows))

        blocks, singles = block_runs(r['duplicates'])
        for b in blocks:
            pairs = ', '.join('#%d+#%d' % (g['ids'][0], g['ids'][1])
                              for g in b['groups'][:3])
            more = len(b['groups']) - 3
            print('    [%s] %s  %s' % ('!' if b['verdict'] == 'DUPLICATE' else '?',
                                       ifc_name(b['class']),
                                       b['type'] or '(no type name)'))
            print('        %s, every pair offset by exactly +%d'
                  % (plural(len(b['groups']), 'pair'), b['offset']))
            print('        -> looks like one duplicated block, not %d separate mistakes'
                  % len(b['groups']))
            print('        %s%s' % (pairs, ', +%d more' % more if more > 0 else ''))
        shown = 0
        for g in singles:
            if shown >= opt.max_rows:
                print('    ... %d more groups (use --json for the full list)'
                      % (len(singles) - shown))
                break
            shown += 1
            print('    [%s] %s x%d  %s' % ('!' if g['verdict'] == 'DUPLICATE' else '?',
                                           ifc_name(g['class']), g['count'],
                                           g['type'] or '(no type name)'))
            print('        %s  ids %s%s' % (
                overlap_words(g['evidence']), ', '.join('#%d' % i for i in g['ids']),
                ' ...' if g['count'] > len(g['ids']) else ''))


def _clash_section(res, opt, lab, lw):
    section('INTERFERENCES   (overlapping, DIFFERENT class or type - not duplicates)')
    print('  Bounding-box overlap >= %.0f%% of the smaller element. A smell test,'
          % (opt.clash_frac * 100))
    print('  not clash detection: connected MEP parts overlap by design.')
    any_i = False
    for r in res:
        if not r['n_interferences']:
            continue
        any_i = True
        pairs = defaultdict(list)
        for h in r['interferences']:
            pairs[tuple(sorted((h['a_class'], h['b_class'])))].append(h)
        print('')
        print('  %s  %s' % (lab[r['file']], plural(r['n_interferences'], 'pair')))
        for k, hs in sorted(pairs.items(), key=lambda kv: -len(kv[1]))[:opt.max_rows]:
            ex = hs[0]
            print('    %4d %-6s %-26s <-> %-26s  e.g. #%d / #%d'
                  % (len(hs), 'pairs' if len(hs) != 1 else 'pair',
                     ifc_name(k[0]), ifc_name(k[1]), ex['a'], ex['b']))
        if r['n_interference_skipped']:
            print('    (%d oversized element(s) skipped)' % r['n_interference_skipped'])
    if not any_i:
        print('  None found.')


def _float_section(res, opt, lab, lw):
    if not any(r['n_floating'] for r in res):
        return
    section('FLOATING / OUT-OF-BUILDING ELEMENTS')
    print('  [!] detached from the model   [?] outlying, but within reach of it')
    print('  "clear" is the gap to the nearest element the fence accepted')
    for r in res:
        if not r['n_floating']:
            continue
        t = r['float_thresholds_m']
        print('')
        print('  %s  %s  (limit %s m in plan, %s m vertically)'
              % (lab[r['file']], plural(r['n_floating'], 'element'),
                 t['plan_m'], t['vertical_m']))
        for fl in r['floating'][:opt.max_rows]:
            print('    [%s] #%-8d %-20s %-24s %-30s %s'
                  % (fl['grade'], fl['id'], ifc_name(fl['class'])[:20],
                     fl['type'][:24], fl['reason'],
                     '%.1f m clear' % fl['clear_m']))
        if r['n_floating'] > opt.max_rows:
            print('    ... %d more' % (r['n_floating'] - opt.max_rows))



def _export_section(res, opt, lab, lw):
    section('EXPORT SETUP   (what the authoring tool wrote into the file header)')
    vw = max([len(r['view_definition'] or '-') for r in res]
             + [len('view definition')])
    print('  %-*s %-*s %s' % (lw, 'model', vw, 'view definition', 'exported by'))
    for r in res:
        print(('  %-*s %-*s %s' % (lw, lab[r['file']], vw,
                                   r['view_definition'] or '-',
                                   r['authoring_tool'] or '-')).rstrip())
    print('')
    # models that share a verdict share a line; nine copies of the same
    # exporter note buries the one model that says something different
    by_text = []
    for r in res:
        sev, text = r['view_status']
        for e in by_text:
            if e[0] == sev and e[1] == text:
                e[2].append(lab[r['file']])
                break
        else:
            by_text.append([sev, text, [lab[r['file']]]])
    for sev, text, who in by_text:
        head = ', '.join(who)
        if len(head) > lw:
            print('  %-4s %s' % ('[%s]' % sev, head))
            print('       %s' % wrap(text, SECTION_W - 8, 7))
        else:
            print('  %-4s %-*s %s' % ('[%s]' % sev, lw, head,
                                      wrap(text, SECTION_W - lw - 9, lw + 8)))
    groups = []
    for r in res:
        bits = []
        if r['exchange_requirement']:
            bits.append('exchange requirement: %s' % r['exchange_requirement'])
        if r['coordinate_reference']:
            bits.append('coordinates: %s' % r['coordinate_reference'])
        if not bits:
            continue
        key = '; '.join(bits)
        for g in groups:
            if g[0] == key:
                g[1].append(lab[r['file']])
                break
        else:
            groups.append([key, [lab[r['file']]]])
    if groups:
        print('')
        for key, who in groups:
            head = ', '.join(who)
            if len(head) > lw:
                print('  %s' % head)
                print('     %s' % wrap(key, SECTION_W - 6, 5))
            else:
                print('  %-*s %s' % (lw, head,
                                     wrap(key, SECTION_W - lw - 4, lw + 3)))


def _class_section(res, opt, lab, lw):
    section('CLASSIFICATION   (IfcClass and PredefinedType on geometric elements)')
    print('  %-*s %-22s %s' % (lw, 'model', 'classified', 'what is left'))
    for r in res:
        c = r['classification']
        if not c['n']:
            print('  %-*s %s' % (lw, lab[r['file']], 'no geometric elements'))
            continue
        pct = 100.0 * c['n_classified'] / c['n']
        bits = []
        if c['n_proxy']:
            bits.append('%d generic proxy' % c['n_proxy'])
        if c['n_fix'] - c['n_proxy'] > 0:
            bits.append('%d with no PredefinedType or ObjectType'
                        % (c['n_fix'] - c['n_proxy']))
        if c['n_generic']:
            bits.append('%d on a generic supertype' % c['n_generic'])
        if c['n_review'] - c['n_generic'] > 0:
            bits.append('%d USERDEFINED or NOTDEFINED'
                        % (c['n_review'] - c['n_generic']))
        flag = ' [!]' if pct < opt.min_classified * 100 else ''
        print(('  %-*s %-22s %s%s' % (
            lw, lab[r['file']], '%d/%d  (%.0f%%)' % (c['n_classified'], c['n'], pct),
            ', '.join(bits) or 'nothing', flag)).rstrip())

    for r in res:
        bad = [m for m in r['classification']['matrix'] if m[2] != PASS]
        if not bad:
            continue
        print('')
        print('  %s' % lab[r['file']])
        shown = sorted(bad, key=lambda m: -m[3])[:opt.max_rows]
        cw = max(len(ifc_name(m[0])) for m in shown)
        pw = max(len(m[1]) for m in shown)
        for cls, pdt, g, n in shown:
            print('    %-4s %-*s %-*s %s'
                  % ('[%s]' % g, cw, ifc_name(cls), pw, pdt,
                     plural(n, 'element')))
        if len(bad) > len(shown):
            print('    ... and %s more' % plural(len(bad) - len(shown), 'combination'))

    bt = [r for r in res if r['n_bad_type_objects']]
    if bt:
        print('')
        for r in bt:
            print('  %-*s %s with PredefinedType USERDEFINED and no ElementType'
                  % (lw, lab[r['file']],
                     plural(r['n_bad_type_objects'], 'type object')))
        print('  USERDEFINED is allowed, but with ElementType blank nothing states')
        print('  what the type is. Assign a proper PredefinedType where one fits.')

    if any(r['classification']['n_scanned'] for r in res):
        print('')
        print('  Some classes are not in the tool\'s attribute table and their')
        print('  PredefinedType was located by shape; those rows are marked in')
        print('  the Classification sheet.')


def _diag_section(res, opt, lab, lw):
    section('DIAGNOSTICS   (how well the tool could read each model)')
    print('  %-*s %-22s %s' % (lw, 'model', 'body geometry', 'notes'))
    for r in res:
        pct = 100.0 * r['n_with_body_geometry'] / r['n_elements'] if r['n_elements'] else 0
        notes = []
        if r['n_aggregate_containers']:
            notes.append('%d aggregate container(s) audited via their parts'
                         % r['n_aggregate_containers'])
        if r['unhandled_geometry']:
            notes.append('unresolved: ' + ', '.join('%s x%d' % (ifc_name(k), v)
                         for k, v in r['unhandled_geometry'].items()))
        flag = ' [!]' if pct < opt.min_geometry * 100 else ''
        shown = '%.0f' % pct if pct in (0.0, 100.0) else '%.1f' % pct
        print(('  %-*s %-22s %s%s' % (
            lw, lab[r['file']],
            '%d/%d  (%s%%)' % (r['n_with_body_geometry'], r['n_elements'], shown),
            '; '.join(notes), flag)).rstrip())
    skipped = [r for r in res if r.get('n_dup_skipped')]
    if skipped:
        print('  Elements whose body geometry could not be read have only a')
        print('  placement origin - a point, not an extent - so they are left out')
        print('  of the duplicate check rather than graded on a position that')
        print('  says nothing. Not checked for duplicates:')
        for r in skipped:
            print('    %-8s %s' % (lab[r['file']],
                                   plural(r['n_dup_skipped'], 'element')))
    fl_any = [r for r in res if r['float_thresholds_m']]
    if fl_any:
        print('  Floating limits are median + %g x MAD of each element centroid'
              % opt.float_k)
        print('  distance from the model centre:')
        for r in fl_any:
            t = r['float_thresholds_m']
            print('    %-*s plan %s m (%s), vertical %s m (%s)'
                  % (lw, lab[r['file']], t['plan_m'], t['plan_source'],
                     t['vertical_m'], t['vertical_source']))




# ----------------------------------------------------------------------------
# Minimal .xlsx writer
#
# Written straight to the OOXML package with zipfile so the tool keeps its
# no-install promise - the people who run this are told only to install Python.
# Strings are written inline, which skips the shared-string table entirely.
# ----------------------------------------------------------------------------

S_PLAIN, S_TITLE, S_SUB, S_HEAD, S_FIX, S_REVIEW, S_PASS, S_WRAP, S_NUM = range(9)
RE_SHEET_BAD = re.compile('[' + re.escape(chr(92) + '/*?:[]') + ']')

_CONTENT_TYPES = (
    '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
    '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">'
    '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>'
    '<Default Extension="xml" ContentType="application/xml"/>'
    '<Override PartName="/xl/workbook.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/>'
    '<Override PartName="/xl/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.styles+xml"/>'
    '%s</Types>')

_ROOT_RELS = (
    '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
    '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
    '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="xl/workbook.xml"/>'
    '</Relationships>')

_STYLES = (
    '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
    '<styleSheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">'
    '<numFmts count="1"><numFmt numFmtId="164" formatCode="0.000"/></numFmts>'
    '<fonts count="4">'
    '<font><sz val="11"/><name val="Calibri"/></font>'
    '<font><b/><sz val="11"/><name val="Calibri"/></font>'
    '<font><b/><sz val="16"/><name val="Calibri"/></font>'
    '<font><b/><sz val="11"/><color rgb="FFFFFFFF"/><name val="Calibri"/></font>'
    '</fonts>'
    '<fills count="6">'
    '<fill><patternFill patternType="none"/></fill>'
    '<fill><patternFill patternType="gray125"/></fill>'
    '<fill><patternFill patternType="solid"><fgColor rgb="FF1F3864"/><bgColor indexed="64"/></patternFill></fill>'
    '<fill><patternFill patternType="solid"><fgColor rgb="FFF4C7C3"/><bgColor indexed="64"/></patternFill></fill>'
    '<fill><patternFill patternType="solid"><fgColor rgb="FFFFE699"/><bgColor indexed="64"/></patternFill></fill>'
    '<fill><patternFill patternType="solid"><fgColor rgb="FFD9EAD3"/><bgColor indexed="64"/></patternFill></fill>'
    '</fills>'
    '<borders count="1"><border><left/><right/><top/><bottom/><diagonal/></border></borders>'
    '<cellStyleXfs count="1"><xf numFmtId="0" fontId="0" fillId="0" borderId="0"/></cellStyleXfs>'
    '<cellXfs count="9">'
    '<xf numFmtId="0" fontId="0" fillId="0" borderId="0" xfId="0"/>'
    '<xf numFmtId="0" fontId="2" fillId="0" borderId="0" xfId="0" applyFont="1"/>'
    '<xf numFmtId="0" fontId="1" fillId="0" borderId="0" xfId="0" applyFont="1"/>'
    '<xf numFmtId="0" fontId="3" fillId="2" borderId="0" xfId="0" applyFont="1" applyFill="1"/>'
    '<xf numFmtId="0" fontId="1" fillId="3" borderId="0" xfId="0" applyFont="1" applyFill="1"/>'
    '<xf numFmtId="0" fontId="1" fillId="4" borderId="0" xfId="0" applyFont="1" applyFill="1"/>'
    '<xf numFmtId="0" fontId="0" fillId="5" borderId="0" xfId="0" applyFill="1"/>'
    '<xf numFmtId="0" fontId="0" fillId="0" borderId="0" xfId="0" applyAlignment="1">'
    '<alignment vertical="top" wrapText="1"/></xf>'
    '<xf numFmtId="164" fontId="0" fillId="0" borderId="0" xfId="0" applyNumberFormat="1"/>'
    '</cellXfs>'
    '<cellStyles count="1"><cellStyle name="Normal" xfId="0" builtinId="0"/></cellStyles>'
    '</styleSheet>')


def _xesc(t):
    t = str(t).replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
    # control characters are illegal in XML and Excel refuses the file
    return ''.join(c for c in t if c >= ' ' or c in '\t\n')


def _colref(i):
    s = ''
    i += 1
    while i:
        i, r = divmod(i - 1, 26)
        s = chr(65 + r) + s
    return s


def _cell(ref, value, style):
    st = ' s="%d"' % style if style else ''
    if value is None or value == '':
        return '<c r="%s"%s/>' % (ref, st) if st else ''
    if isinstance(value, bool):
        value = str(value)
    if isinstance(value, (int, float)):
        return '<c r="%s"%s><v>%s</v></c>' % (ref, st, repr(value))
    return ('<c r="%s"%s t="inlineStr"><is><t xml:space="preserve">%s</t></is></c>'
            % (ref, st, _xesc(value)))


def _sheet_xml(rows, header_row, widths):
    body = []
    for ri, row in enumerate(rows):
        cells = []
        for ci, cv in enumerate(row):
            value, style = cv if isinstance(cv, tuple) else (cv, S_PLAIN)
            c = _cell('%s%d' % (_colref(ci), ri + 1), value, style)
            if c:
                cells.append(c)
        body.append('<row r="%d">%s</row>' % (ri + 1, ''.join(cells)))
    ncol = max([len(r) for r in rows] + [1])
    cols = ''.join('<col min="%d" max="%d" width="%.1f" customWidth="1"/>'
                   % (i + 1, i + 1, widths[i]) for i in range(len(widths)))
    view = '<sheetView workbookViewId="0">'
    if header_row:
        view += ('<pane ySplit="%d" topLeftCell="A%d" activePane="bottomLeft" '
                 'state="frozen"/>' % (header_row, header_row + 1))
    view += '</sheetView>'
    afilter = ''
    if header_row and len(rows) > header_row:
        afilter = ('<autoFilter ref="A%d:%s%d"/>'
                   % (header_row, _colref(ncol - 1), len(rows)))
    return ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
            '<worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">'
            '<dimension ref="A1:%s%d"/><sheetViews>%s</sheetViews>'
            '<sheetFormatPr defaultRowHeight="15"/>%s<sheetData>%s</sheetData>%s'
            '</worksheet>'
            % (_colref(ncol - 1), max(len(rows), 1), view,
               '<cols>%s</cols>' % cols if cols else '', ''.join(body), afilter))


def _widths(rows, cap=70.0):
    n = max([len(r) for r in rows] + [1])
    w = [9.0] * n
    for row in rows:
        for i, cv in enumerate(row):
            value = cv[0] if isinstance(cv, tuple) else cv
            if value is None:
                continue
            w[i] = max(w[i], min(cap, len(str(value)) + 2.5))
    return w


def write_xlsx(path, sheets):
    """sheets: list of (name, rows, header_row).  rows hold values or (value, style)."""
    import zipfile
    parts = []
    wb_sheets = []
    wb_rels = []
    for i, (name, rows, header_row) in enumerate(sheets, start=1):
        safe = re.sub(RE_SHEET_BAD, '-', name)[:31]
        parts.append(('xl/worksheets/sheet%d.xml' % i,
                      _sheet_xml(rows or [['']], header_row, _widths(rows or [['']]))))
        wb_sheets.append('<sheet name="%s" sheetId="%d" r:id="rId%d"/>'
                         % (_xesc(safe), i, i))
        wb_rels.append('<Relationship Id="rId%d" Type="http://schemas.openxmlformats.org'
                       '/officeDocument/2006/relationships/worksheet" '
                       'Target="worksheets/sheet%d.xml"/>' % (i, i))
    overrides = ''.join(
        '<Override PartName="/xl/worksheets/sheet%d.xml" ContentType="application/vnd.'
        'openxmlformats-officedocument.spreadsheetml.worksheet+xml"/>' % i
        for i in range(1, len(sheets) + 1))
    workbook = ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
                '<workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" '
                'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">'
                '<sheets>%s</sheets></workbook>' % ''.join(wb_sheets))
    rels = ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
            '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
            '%s<Relationship Id="rId%d" Type="http://schemas.openxmlformats.org/'
            'officeDocument/2006/relationships/styles" Target="styles.xml"/>'
            '</Relationships>' % (''.join(wb_rels), len(sheets) + 1))
    with zipfile.ZipFile(path, 'w', zipfile.ZIP_DEFLATED) as z:
        z.writestr('[Content_Types].xml', _CONTENT_TYPES % overrides)
        z.writestr('_rels/.rels', _ROOT_RELS)
        z.writestr('xl/workbook.xml', workbook)
        z.writestr('xl/_rels/workbook.xml.rels', rels)
        z.writestr('xl/styles.xml', _STYLES)
        for name, xml in parts:
            z.writestr(name, xml)


# ----------------------------------------------------------------------------
# The audit workbook
# ----------------------------------------------------------------------------

SEV_STYLE = {'!': S_FIX, '?': S_REVIEW, 'ok': S_PASS}

# The three grades never change; only what they are called does.  A profile
# renames them with severity_words, so a report that sits beside a checker
# using FAIL / ALERT / PASS can be read in the same words.
SEV_WORD = {'!': 'FIX', '?': 'REVIEW', 'ok': 'PASS'}   # updated by --profile


def _hdr(*names):
    return [(n, S_HEAD) for n in names]


def excel_report(path, res, opt):
    lab = model_labels(res)
    findings = collect_findings(res, opt, lab)
    package = os.path.commonprefix([r['file'] for r in res]).rstrip('-_ ') or 'package'
    stamp = datetime.datetime.now().strftime('%d %b %Y %H:%M')
    n_fix = sum(1 for f in findings if f['sev'] == '!')
    n_rev = sum(1 for f in findings if f['sev'] == '?')

    # ---- Summary ----
    s1 = [[('IFC PACKAGE AUDIT', S_TITLE)],
          [('Package', S_SUB), package],
          [('Models', S_SUB), len(res)],
          [('Generated', S_SUB), stamp],
          [('Result', S_SUB),
           'no issues found' if not (n_fix or n_rev)
           else ', '.join('%d %s' % (c, SEV_WORD[sv]) for c, sv
                          in ((n_fix, FIX), (n_rev, REVIEW)) if c)],
          [],
          _hdr('Rule', 'Severity', 'Area', 'Rule title', 'Finding',
               'Profile check')]
    head_row = len(s1)
    rc = rule_checks(getattr(opt, 'profile_data', None))
    for f in findings:
        s1.append([f['id'], (SEV_WORD[f['sev']], SEV_STYLE[f['sev']]),
                   f['area'], f['title'], (f['text'], S_WRAP),
                   ', '.join(rc.get(f['id'], ()))])

    # ---- Models ----
    s2 = [_hdr('Model', 'File', 'Schema', 'View definition', 'MVD check',
               'Exchange requirement', 'Exported by', 'Length unit', 'Elements',
               'Body geometry', 'Coverage %', 'Classified', 'Classified %',
               'CRS', 'Ref latitude',
               'Local centre X', 'Local centre Y', 'World E', 'World N',
               'Georeferencing', 'MapConv E', 'MapConv N', 'MapConv H',
               'Grid rotation', 'Scale')]
    for r in res:
        mc = r['map_conversion'] or {}
        c = r['local_centre_m'] or [None, None, None]
        wc = r['world_centre_ENH'] or [None, None, None]
        cov = (100.0 * r['n_with_body_geometry'] / r['n_elements']) if r['n_elements'] else None
        cl = r['classification']
        clp = (100.0 * cl['n_classified'] / cl['n']) if cl['n'] else None
        # an empty model has nothing to classify, so it is never 'below target'
        s2.append([lab[r['file']], r['file'], r['schema'],
                   r['view_definition'] or '(none declared)',
                   (SEV_WORD[r['view_status'][0]], SEV_STYLE[r['view_status'][0]]),
                   r['exchange_requirement'] or '', r['authoring_tool'] or '',
                   r['length_unit'],
                   r['n_elements'], r['n_with_body_geometry'],
                   (round(cov, 1) if cov is not None else None,
                    S_FIX if cov is not None and cov < opt.min_geometry * 100 else S_PLAIN),
                   cl['n_classified'],
                   (round(clp, 1) if clp is not None else None,
                    S_FIX if clp is not None and clp < opt.min_classified * 100
                    else S_PLAIN),
                   r['projected_crs'], r['ref_lat'], c[0], c[1],
                   (wc[0], S_NUM), (wc[1], S_NUM),
                   (r['map_conversion_status'],
                    S_FIX if r['map_conversion_status'] != 'set' else S_PLAIN),
                   (mc.get('eastings'), S_NUM), (mc.get('northings'), S_NUM),
                   (mc.get('height'), S_NUM), r['grid_rotation_deg'],
                   1.0 if mc.get('scale') is None and mc else mc.get('scale')])

    # ---- Duplicates ----
    s3 = [_hdr('Model', 'Severity', 'Finding', 'IFC class', 'Type / family',
               'Elements', 'Evidence', 'Element IDs', 'Source tags')]
    for r in res:
        for g, c, det in r['dup_guid_detail']:
            s3.append([lab[r['file']], ('FIX', S_FIX), 'Reused GlobalId', '', g, c,
                       'GlobalId must be unique in the file',
                       ', '.join('#%d' % d[0] for d in det), ''])
        blocks, singles = block_runs(r['duplicates'])
        for b in blocks:
            s3.append([lab[r['file']],
                       ('FIX' if b['verdict'] == 'DUPLICATE' else 'REVIEW',
                        SEV_STYLE['!' if b['verdict'] == 'DUPLICATE' else '?']),
                       'Duplicated block', ifc_name(b['class']),
                       b['type'] or '(no type name)', len(b['groups']) * 2,
                       'every pair offset by exactly +%d - one copied block, '
                       'not %d separate mistakes' % (b['offset'], len(b['groups'])),
                       ', '.join('#%d+#%d' % (g['ids'][0], g['ids'][1])
                                 for g in b['groups']), ''])
        for g in singles:
            s3.append([lab[r['file']],
                       ('FIX' if g['verdict'] == 'DUPLICATE' else 'REVIEW',
                        SEV_STYLE['!' if g['verdict'] == 'DUPLICATE' else '?']),
                       'Duplicate', ifc_name(g['class']),
                       g['type'] or '(no type name)', g['count'],
                       overlap_words(g['evidence']),
                       ', '.join('#%d' % i for i in g['ids']),
                       ', '.join(g['tags'])])

    # ---- Georeferencing ----
    anchors = [(r, georef_anchor(r)) for r in res
               if r['site_origin_m'] or r['map_conversion']]
    mid = [median([a[1][k] for a in anchors]) for k in range(3)] if anchors else [0, 0, 0]
    sg = [_hdr('Model', 'LoGeoRef', 'Method', 'MapConversion', 'CRS',
               'Anchor E (m)', 'Anchor N (m)', 'Anchor H (m)',
               'Off E (mm)', 'Off N (mm)', 'Off H (mm)', 'Action')]
    for r in res:
        a = georef_anchor(r)
        lvl = georef_level(r)
        off = [(a[k] - mid[k]) * 1000.0 for k in range(3)]
        bad = max(abs(o) for o in off) > opt.geo_tol
        sg.append([lab[r['file']], (lvl, S_FIX if lvl < 50 else S_PLAIN), LOGEOREF[lvl],
                   (r['map_conversion_status'],
                    S_FIX if r['map_conversion_status'] != 'set' else S_PLAIN),
                   r['projected_crs'], (a[0], S_NUM), (a[1], S_NUM), (a[2], S_NUM),
                   (round(off[0], 1), S_FIX if bad else S_PLAIN),
                   (round(off[1], 1), S_FIX if bad else S_PLAIN),
                   (round(off[2], 1), S_FIX if bad else S_PLAIN),
                   ('Re-export as IFC4 or later first - this schema has no '
                    'IfcMapConversion'
                    if not can_map_convert(r['schema'])
                    else 'Re-export with a real IfcMapConversion')
                   if lvl < 50 else 'OK'])
    advice = georef_advice(res, lab)
    if advice:
        sg.append([])
        sg.append([('HOW TO FIX', S_SUB)])
        for line in advice:
            sg.append([line])

    sheets = [('Summary', s1, head_row), ('Models', s2, 1),
              ('Georeferencing', sg, 1), ('Duplicates', s3, 1)]

    # ---- Spatial structure ----
    # One row per storey per model, with the level group each one fell into:
    # sorting the sheet by that column puts the storeys that are meant to be
    # the same level next to each other, which is where a naming disagreement
    # becomes obvious.
    groups = level_groups(res, lab, opt.storey_tol / 1000.0)
    split, drift = storey_conflicts(groups, opt.storey_datum / 1000.0,
                                    opt.storey_tol / 1000.0,
                                    _anchor_offsets(res, lab))
    drift_keys = dict((norm_storey(d['name']), d) for d in drift)
    grp_of = {}
    for g in groups:
        for n in g['names']:
            for l, s in n['rows']:
                grp_of[(l, s['id'])] = (g, n)
    ss = [_hdr('Model', 'Storey', 'Long name', 'Elevation attribute (m)',
               'Project Z (m)', 'Level in survey datum (m)',
               'Level of the package (m)', 'Agreement', 'Why',
               'Also called', 'Elements', 'Spaces', 'Composition')]
    for r in res:
        for s in r['spatial']['storeys']:
            g, n = grp_of.get((lab[r['file']], s['id']), (None, None))
            d = drift_keys.get(norm_storey(s['name']))
            sev = None
            why = ''
            if d and d['anchor']:
                sev, why = REVIEW, ('this name is used at another level, by '
                                    'the amount the models disagree about '
                                    'their own survey height - see G05')
            elif d and not d['datum']:
                sev, why = FIX, 'this name is used at another level'
            elif d:
                sev, why = REVIEW, ('this name is used at a level %.0f mm '
                                    'away, which is datum-sized - finished '
                                    'floor level against top of concrete'
                                    % (d['spread_m'] * 1000.0))
            elif g is not None and len(g['names']) > 1:
                sev, why = REVIEW, 'this level has another name in another model'
            others = '' if g is None else ', '.join(
                '%s (%s)' % (o['name'], ', '.join(o['models']))
                for o in g['names'] if o['key'] != n['key'])
            ss.append([lab[r['file']], s['name'], s['long_name'],
                       s['elevation_m'], s['z_m'], s['level_m'],
                       None if g is None else round(g['z'], 4),
                       (SEV_WORD[sev] if sev else 'OK',
                        SEV_STYLE[sev] if sev else S_PLAIN),
                       (why, S_WRAP),
                       others, s['n_elements'], s['n_spaces'],
                       s['composition'] or ''])
    for r in res:
        for p in r['spatial']['hierarchy']['problems']:
            ss.append([lab[r['file']], '(hierarchy)', '', None, None, None,
                       None, (SEV_WORD[FIX], S_FIX), (p, S_WRAP), '',
                       None, None, ''])
    if len(ss) > 1:
        sheets.append(('Spatial structure', ss, 1))

    # ---- Elements not on a storey ----
    if any(r['spatial']['n_loose'] or r['spatial']['n_above_storey'] for r in res):
        su = [_hdr('Model', 'Severity', 'Element', 'IFC class', 'Type / family',
                   'Held by', 'Why it matters')]
        for r in res:
            for x in r['spatial']['loose']:
                su.append([lab[r['file']], (SEV_WORD[FIX], S_FIX),
                           '#%d' % x['id'], ifc_name(x['class']), x['type'],
                           'nothing',
                           ('in no IfcRelContainedInSpatialStructure, so it is '
                            'on no level and is skipped by anything that walks '
                            'the model by storey', S_WRAP)])
            for x in r['spatial']['above_storey']:
                su.append([lab[r['file']], (SEV_WORD[REVIEW], S_REVIEW),
                           '#%d' % x['id'], ifc_name(x['class']), x['type'],
                           x['container'],
                           ('contained above storey level - correct for '
                            'external works and for anything spanning the '
                            'building, worth confirming otherwise', S_WRAP)])
        sheets.append(('Elements off storey', su, 1))

    # ---- Classification ----
    s7 = [_hdr('Model', 'Severity', 'Element', 'IFC class', 'PredefinedType',
               'Type PredefinedType', 'ObjectType', 'Type / family',
               'Read by', 'Why', 'What to do')]
    for r in res:
        for row in r['classification']['rows']:
            s7.append([lab[r['file']],
                       (SEV_WORD[row['grade']], SEV_STYLE[row['grade']]),
                       '#%d' % row['id'], ifc_name(row['class']),
                       row['predefined'] or '(absent)',
                       row['type_predefined'] or '', row['object_type'] or '',
                       row['type_name'], row['read_by'],
                       (row['why'], S_WRAP), (row['action'], S_WRAP)])
        for b in r['bad_type_objects']:
            s7.append([lab[r['file']], ('REVIEW', S_REVIEW), '#%d' % b['id'],
                       ifc_name(b['class']), 'USERDEFINED', '', '', b['name'],
                       'index',
                       ('USERDEFINED with no ElementType, so nothing states '
                        'what this type is', S_WRAP),
                       ('assign a proper PredefinedType, or name the type in '
                        'ElementType', S_WRAP)])
    if len(s7) > 1:
        sheets.append(('Classification', s7, 1))

    # ---- Interferences ----
    if opt.clash and any(r['n_interferences'] for r in res):
        s4 = [_hdr('Model', 'Class A', 'Class B', 'Pairs', 'Example A', 'Example B')]
        s5 = [_hdr('Model', 'Element A', 'Class A', 'Type A',
                   'Element B', 'Class B', 'Type B', 'Overlap % of smaller')]
        for r in res:
            pairs = defaultdict(list)
            for h in r['interferences']:
                pairs[tuple(sorted((h['a_class'], h['b_class'])))].append(h)
            for k, hs in sorted(pairs.items(), key=lambda kv: -len(kv[1])):
                s4.append([lab[r['file']], ifc_name(k[0]), ifc_name(k[1]), len(hs),
                           '#%d' % hs[0]['a'], '#%d' % hs[0]['b']])
            for h in r['interferences']:
                s5.append([lab[r['file']], '#%d' % h['a'], ifc_name(h['a_class']),
                           h['a_type'], '#%d' % h['b'], ifc_name(h['b_class']),
                           h['b_type'], round(h['overlap_frac'] * 100, 1)])
        sheets.append(('Interferences by type', s4, 1))
        sheets.append(('Interference pairs', s5, 1))

    # ---- Floating ----
    if any(r['n_floating'] for r in res):
        s6 = [_hdr('Model', 'Severity', 'Element', 'IFC class', 'Type / family',
                   'Distance in plan (m)', 'Distance vertical (m)',
                   'Clear of the rest (m)', 'x spread of the rest',
                   'Why flagged', 'Verdict')]
        for r in res:
            for fl in r['floating']:
                s6.append([lab[r['file']],
                           (SEV_WORD[fl['grade']], SEV_STYLE[fl['grade']]),
                           '#%d' % fl['id'], ifc_name(fl['class']),
                           fl['type'], fl['plan_m'], fl['vert_m'],
                           fl['clear_m'], fl['spread_ratio'], fl['reason'],
                           (fl['verdict'], S_WRAP)])
        sheets.append(('Floating', s6, 1))

    write_xlsx(path, sheets)
    return [s[0] for s in sheets]


# ----------------------------------------------------------------------------
# CLI
# ----------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description='openBIM / IFC model-package review tool')
    ap.add_argument('paths', nargs='*', default=['.'])
    ap.add_argument('--json', help='also write the raw findings to this file')
    ap.add_argument('--excel', metavar='FILE.xlsx',
                    help='also write a shareable Excel workbook (no add-ins needed)')
    ap.add_argument('--float-xy', type=float, default=None, metavar='M',
                    help='absolute plan float threshold in metres from the model '
                         'centre (default: derived from the model)')
    ap.add_argument('--float-z', type=float, default=None, metavar='M',
                    help='absolute vertical float threshold in metres from the model '
                         'centre (default: derived from the model)')
    ap.add_argument('--float-k', type=float, default=8.0,
                    help='float sensitivity: flag beyond median + K x MAD of the '
                         'distance from centre; lower is stricter (default 8)')
    ap.add_argument('--float-detach', type=float, default=4.0,
                    help='a flagged element displaced by more than this many '
                         'times the spread of the rest is graded FIX rather '
                         'than REVIEW (default 4)')
    ap.add_argument('--float-min', type=float, default=10.0,
                    help='floor for the derived float thresholds, metres (default 10)')
    ap.add_argument('--dup-tol', type=float, default=10.0,
                    help='coincidence tolerance in mm (default 10)')
    ap.add_argument('--dup-iou', type=float, default=0.90,
                    help='bbox IoU at or above which a pair is a DUPLICATE (default 0.90)')
    ap.add_argument('--probable-iou', type=float, default=0.50,
                    help='bbox IoU at or above which a pair is PROBABLE (default 0.50)')
    ap.add_argument('--clash', action='store_true',
                    help='also report overlapping elements of different class/type')
    ap.add_argument('--clash-frac', type=float, default=0.30,
                    help='overlap fraction of the smaller element to report (default 0.30)')
    ap.add_argument('--geo-tol', type=float, default=1.0,
                    help='MapConversion agreement tolerance in mm (default 1)')
    ap.add_argument('--storey-tol', type=float, default=50.0,
                    help='storeys within this many mm of each other are read '
                         'as the same level of the package (default 50)')
    ap.add_argument('--storey-datum', type=float, default=600.0,
                    help='a storey name found at two levels further apart than '
                         '--storey-tol but within this many mm is reported as '
                         'a datum difference to confirm - finished floor level '
                         'against top of concrete - rather than as a fault '
                         '(default 600)')
    ap.add_argument('--min-geometry', type=float, default=0.90,
                    help='flag a model whose resolved-geometry share falls below '
                         'this fraction (default 0.90)')
    ap.add_argument('--min-classified', type=float, default=0.90,
                    help='flag a model whose share of elements with a specific '
                         'PredefinedType falls below this fraction (default 0.90)')
    ap.add_argument('--expect-schema', metavar='SCHEMA',
                    help='require every model to be on this schema, e.g. IFC4X3; '
                         'without it the majority schema in the package is used')
    ap.add_argument('--expect-view', metavar='NAME',
                    help='require every model to declare this ViewDefinition, '
                         'e.g. ReferenceView_V1.2')
    ap.add_argument('--max-rows', type=int, default=20,
                    help='max rows printed per section per model (default 20)')
    ap.add_argument('--profile', metavar='FILE.json',
                    help='apply a submission profile: a JSON file stating what '
                         'this project, client or authority asks for - schema, '
                         'MVD, thresholds, the words for the three grades, and '
                         'the external checklist to report against.  Options '
                         'you pass yourself always win')
    ap.add_argument('--rules', action='store_true',
                    help='print the rule table and exit; no model needed')
    opt = ap.parse_args()
    opt.skipped = []

    if opt.rules:
        print_rules()
        return

    # which options the caller actually stated, so a profile fills in the rest
    # without ever overriding something they asked for by name
    blank = ap.parse_args([])
    opt.explicit = set(k for k, v in vars(opt).items()
                       if getattr(blank, k, None) != v)
    try:
        apply_profile(opt)
    except (ValueError, IOError, OSError) as e:
        print('Could not use profile %s:' % opt.profile)
        print('  %s' % e)
        sys.exit(2)

    files = []
    for p in opt.paths:
        if os.path.isdir(p):
            for pat in ('*.ifc', '*.IFC'):
                files += glob.glob(os.path.join(p, pat))
        elif p.lower().endswith('.ifc'):
            files.append(p)
    seen = {}
    for f in files:                       # dedupe case-insensitively, keep real name
        seen.setdefault(os.path.normcase(os.path.abspath(f)), f)
    files = [seen[k] for k in sorted(seen)]
    if not files:
        print('No .ifc files found.')
        sys.exit(1)

    res = []
    opt.skipped = []
    for f in files:
        sys.stderr.write('reading %s ...\n' % os.path.basename(f))
        try:
            res.append(audit_file(f, opt))
        except (IOError, OSError) as e:
            opt.skipped.append((os.path.basename(f), str(e)))
            sys.stderr.write('  SKIPPED: %s\n' % e)
    if not res:
        print('No .ifc file could be read.')
        for name, why in opt.skipped:
            print('  %s: %s' % (name, why))
        sys.exit(1)
    report(res, opt)

    if opt.json:
        # v4 wraps what v3 dumped as a bare list.  The findings carry the rule
        # ids, and a list has nowhere to put them.
        doc = {'tool': 'ifc_audit v4',
               'generated': datetime.datetime.now().isoformat(timespec='seconds'),
               # which requirement revision this was run against, not just
               # the path it was read from - a report that cannot say that is
               # not evidence of anything a year later
               'profile': None if not opt.profile_data else
                          {'file': opt.profile,
                           'name': opt.profile_data.get('name'),
                           'version': opt.profile_data.get('version'),
                           'checks': opt.profile_data.get('checks')},
               'rules': [RULE[r[0]] for r in RULES],
               'findings': collect_findings(res, opt, model_labels(res)),
               'models': res}
        with open(opt.json, 'w', encoding='utf-8') as fh:
            json.dump(doc, fh, indent=1, default=str)
        print('Raw JSON -> %s' % opt.json)

    if opt.excel:
        name = opt.excel if opt.excel.lower().endswith('.xlsx') else opt.excel + '.xlsx'
        try:
            tabs = excel_report(name, res, opt)
        except OSError as e:
            print('Could not write %s: %s' % (name, e))
        else:
            print('Excel report -> %s   (%s)' % (name, ', '.join(tabs)))

    support_footer()


if __name__ == '__main__':
    main()
