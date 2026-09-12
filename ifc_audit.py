#!/usr/bin/env python3
"""
ifc_audit.py - openBIM / IFC model-package review tool.  (v2)

Checks a folder (or list) of .ifc files for:
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
  * Cross-file consistency: schema/unit mix, and - most importantly - whether
    the models agree on their IfcMapConversion, which is what actually decides
    whether a federated package lines up.  An all-zero IfcMapConversion is
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
"""
import re, sys, os, json, math, glob, argparse, datetime
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

class Model:
    """A parsed IFC file: only the entities needed for geolocation + geometry."""

    def __init__(self, path):
        self.path = path
        self.name = os.path.basename(path)
        self.ent = {}                 # id -> (TYPE, [args])
        self.schema = '?'
        self.unit_name = None         # e.g. 'MILLIMETRE'
        self.to_mm = None             # project length unit -> millimetres
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
        self.unhandled = Counter()
        self._bbcache = {}
        self._mcache = {}
        self._load()

    # -- parsing -------------------------------------------------------------

    def _load(self):
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
                    if sval(arg(a, 12)) or sval(arg(a, 13)):
                        self.has_address = True
                    self._count_guid(sval(arg(a, 0)), rec[0], typ)
                    continue
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

                if typ == 'IFCRELAGGREGATES':
                    rec = parse_record(line)
                    a = split_args(rec[2])
                    parent = ref(arg(a, 4))
                    if parent is not None:
                        self.decomposed.add(parent)

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
                if typ.endswith('TYPE') or typ.startswith('IFCREL') \
                        or 'PROPERTY' in typ or 'MATERIAL' in typ or typ in EXCLUDE:
                    continue
                raw_elems.append((eid, typ, line))

        self._resolve_units(proj_units)
        self._resolve_map_unit()
        self._resolve_context(ctx_ids)
        self._build_elements(raw_elems)
        if self.site_place and self.site_place[0] is not None:
            self.site_origin = self.placement(self.site_place[0])[1]

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
        for eid, typ, line in raw_elems:
            a = split_args(parse_record(line)[2])
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
            self.elements.append(Element(eid, typ, name, otype, tag, place, shape))
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
        e = self.ent.get(i)
        if not e or depth > 24:
            return None
        t, a = e
        if t == 'IFCINDEXEDPOLYCURVE':
            pl = self.ent.get(ref(arg(a, 0)))
            return bb_points(point_rows(arg(pl[1], 0))) if pl else None
        if t == 'IFCPOLYLINE':
            return bb_points(p for p in (self._pt(r) for r in reflist(arg(a, 0))) if p)
        if t == 'IFCPOLYLOOP':
            return bb_points(p for p in (self._pt(r) for r in reflist(arg(a, 0))) if p)
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
            # first operand only: the second is a cutting tool and may be huge
            return self.item_bb(ref(arg(a, 1)), depth + 1)

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
                 'shape_id', 'bbox', 'source')

    def __init__(self, eid, cls, name, otype, tag, place_id, shape_id):
        self.id = eid
        self.ifc_class = cls
        self.name = name
        self.object_type = otype
        self.tag = tag
        self.place_id = place_id
        self.shape_id = shape_id
        self.bbox = None
        self.source = 'none'    # 'body' | 'placement' | 'none'

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

    out = []
    for e, pd, vd in zip(elems, dp, dz):
        if pd <= thr_p and vd <= thr_z:
            continue
        why = []
        if pd > thr_p:
            why.append('%.0f m from centre in plan' % pd)
        if vd > thr_z:
            why.append('%.1f m from centre vertically' % vd)
        out.append({'id': e.id, 'class': e.ifc_class, 'type': e.label()[:70],
                    'plan_m': round(pd, 1), 'vert_m': round(vd, 1),
                    'reason': ' and '.join(why)})
    out.sort(key=lambda r: -(r['plan_m'] ** 2 + r['vert_m'] ** 2))
    thresholds = {'plan_m': round(thr_p, 1), 'vertical_m': round(thr_z, 1),
                  'plan_source': how_p, 'vertical_source': how_z,
                  'median_plan_m': round(median(dp), 1),
                  'median_vertical_m': round(median(dz), 1)}
    return out, (cx, cy, cz), thresholds


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
    dup_groups, _ = find_duplicates(m, elems, tol, opt.dup_iou, opt.probable_iou)
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

    site = m.site[0] if m.site else (None, None, None, '')
    return {
        'file': m.name, 'schema': m.schema,
        'length_unit': m.unit_name, 'unit_to_mm': m.to_mm, 'unit_assumed_mm': unit_assumed,
        'true_north_deg': m.true_north, 'wcs_offset': m.wcs_offset,
        'ref_lat': site[0], 'ref_long': site[1], 'ref_elev': site[2],
        'n_sites': len(m.site),
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
           'Stack Terminal', 'StackTerminal', 'WasteTerminal', 'Grid', 'Annotation'):
    IFC_NAMES['IFC' + _n.replace(' ', '').upper()] = 'Ifc' + _n.replace(' ', '')


def ifc_name(cls):
    """IFCPIPEFITTING -> IfcPipeFitting (all upper case is hard to skim)."""
    if not cls:
        return '-'
    known = IFC_NAMES.get(cls.upper())
    if known:
        return known
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


def collect_findings(res, opt, lab):
    """Everything the reader must decide on, worst first."""
    f = []
    n = len(res)

    def add(sev, area, text):
        f.append({'sev': sev, 'area': area, 'text': text})

    # --- schema / units / CRS ---
    schemas = sorted(set(r['schema'] for r in res))
    if len(schemas) > 1:
        add(FIX, 'Schema', 'mixed: ' + ', '.join(schemas))
    else:
        add(PASS, 'Schema', '%s throughout' % schemas[0])

    units = sorted(set(str(r['length_unit']) for r in res))
    if len(units) > 1:
        by_u = defaultdict(list)
        for r in res:
            by_u[str(r['length_unit'])].append(lab[r['file']])
        add(FIX, 'Units', 'mixed: ' + '; '.join(
            '%s in %s' % (u, ', '.join(by_u[u])) for u in units))
    else:
        add(PASS, 'Units', '%s throughout' % units[0])

    crss = sorted(set(str(r['projected_crs']) for r in res))
    if len(crss) > 1:
        add(FIX, 'CRS', 'mixed: ' + ', '.join(crss))
    elif crss[0] == 'None':
        add(REVIEW, 'CRS', 'no IfcProjectedCRS declared in any model')
    else:
        add(PASS, 'CRS', '%s throughout' % crss[0])

    # --- georeferencing ---
    st = {r['file']: r['map_conversion_status'] for r in res}
    n_set = sum(1 for v in st.values() if v == 'set')
    n_ph = sum(1 for v in st.values() if v == 'placeholder')
    n_abs = sum(1 for v in st.values() if v == 'absent')
    lv = {r['file']: georef_level(r) for r in res}
    worst_lv = min(lv.values())
    if worst_lv >= 50:
        add(PASS, 'Georeferencing', 'IfcMapConversion + IfcProjectedCRS in all %d models' % n)
    elif worst_lv >= 30:
        # positioned, but by a mechanism that carries no declaration of intent
        add(REVIEW, 'Georeferencing',
            'positioned by the IfcSite placement, not IfcMapConversion (LoGeoRef %d); '
            '%s left at all zeros - see HOW TO FIX'
            % (worst_lv, plural(n_ph, 'MapConversion') if n_ph else 'no MapConversion'))
    else:
        add(FIX, 'Georeferencing',
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
            add(FIX, 'Georeferencing',
                'MapConversion %s differs by %.1f mm across %d models'
                % (which, worst * mu, len(with_mc)))
        else:
            add(PASS, 'Georeferencing',
                'all %d MapConversions agree within %.0f mm' % (len(with_mc), opt.geo_tol))

    bad_scale = [lab[r['file']] for r in with_mc
                 if expected_scale(r['unit_to_mm'], r['map_unit_to_mm'])
                 and abs((1.0 if r['map_conversion']['scale'] is None
                          else r['map_conversion']['scale'])
                         - expected_scale(r['unit_to_mm'], r['map_unit_to_mm']))
                 > expected_scale(r['unit_to_mm'], r['map_unit_to_mm']) * 1e-6]
    if bad_scale:
        add(FIX, 'Georeferencing',
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
            add(FIX, 'Site anchor',
                'models do not share one survey point: spread %.3f m; %s is off by '
                'E %.3f, N %.3f, H %.3f m'
                % (worst, lab[far[0]['file']], off[0], off[1], off[2]))
        else:
            add(PASS, 'Site anchor',
                'all %d models share one survey point (within %.0f mm)'
                % (len(anchors), opt.geo_tol))

    # --- duplicates ---
    guid = [(lab[r['file']], r['dup_guid_extra']) for r in res if r['dup_guid_extra']]
    if guid:
        add(FIX, 'GlobalIds', 'repeated GlobalId (invalid file) in %s'
            % ', '.join('%s (%d)' % g for g in guid))

    dup = [(lab[r['file']], r['n_duplicate_extra']) for r in res if r['n_duplicate_extra']]
    if dup:
        add(FIX, 'Duplicates', '%s in %s'
            % (plural(sum(d[1] for d in dup), 'duplicated element'),
               brief(dup)))
    else:
        add(PASS, 'Duplicates', 'none found')

    prob = [(lab[r['file']], r['n_probable_groups']) for r in res if r['n_probable_groups']]
    if prob:
        add(REVIEW, 'Probable dups', '%s that could not be confirmed in %s'
            % (plural(sum(p[1] for p in prob), 'group'),
               brief(prob)))

    # --- geometry coverage ---
    low = [(lab[r['file']], 100.0 * r['n_with_body_geometry'] / r['n_elements'])
           for r in res if r['n_elements']
           and r['n_with_body_geometry'] < r['n_elements'] * opt.min_geometry]
    if low:
        add(FIX, 'Geometry', 'geometry unresolved for a large share of %s'
            % ', '.join('%s (%.0f%% resolved)' % l for l in low))

    # --- floating ---
    fl = [(lab[r['file']], r['n_floating']) for r in res if r['n_floating']]
    if fl:
        add(FIX, 'Floating', '%s far outside the model in %s'
            % (plural(sum(x[1] for x in fl), 'element'),
               brief(fl)))
    else:
        add(PASS, 'Floating', 'none found')

    # --- interferences (informational) ---
    if opt.clash:
        it = [(lab[r['file']], r['n_interferences']) for r in res if r['n_interferences']]
        if it:
            add(REVIEW, 'Interferences', '%s of overlapping different-type elements in %s'
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
        print(' %-4s %-15s %s' % ('[%s]' % f['sev'], f['area'],
                                   wrap(f['text'], SECTION_W - 22, 22)))

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

    _geo_section(res, opt, lab, lw)
    _dup_section(res, opt, lab, lw)
    if opt.clash:
        _clash_section(res, opt, lab, lw)
    _float_section(res, opt, lab, lw)
    _diag_section(res, opt, lab, lw)
    print('')


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
        print('  More than one IfcSite in %s   [!]' % ', '.join(multi))

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
    for r in res:
        if not r['n_floating']:
            continue
        t = r['float_thresholds_m']
        print('')
        print('  %s  %s  (limit %s m in plan, %s m vertically)'
              % (lab[r['file']], plural(r['n_floating'], 'element'),
                 t['plan_m'], t['vertical_m']))
        for fl in r['floating'][:opt.max_rows]:
            print('    [!] #%-8d %-22s %-34s %s'
                  % (fl['id'], ifc_name(fl['class']), fl['type'][:34], fl['reason']))
        if r['n_floating'] > opt.max_rows:
            print('    ... %d more' % (r['n_floating'] - opt.max_rows))


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
    if any(r['n_with_body_geometry'] < r['n_elements'] for r in res):
        print('  Elements without body geometry fall back to their placement origin')
        print('  and can only ever be graded PROBABLE, never DUPLICATE.')
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
SEV_WORD = {'!': 'FIX', '?': 'REVIEW', 'ok': 'PASS'}


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
           else '%d to fix, %d to review' % (n_fix, n_rev)],
          [],
          _hdr('Severity', 'Area', 'Finding')]
    head_row = len(s1)
    for f in findings:
        s1.append([(SEV_WORD[f['sev']], SEV_STYLE[f['sev']]), f['area'],
                   (f['text'], S_WRAP)])

    # ---- Models ----
    s2 = [_hdr('Model', 'File', 'Schema', 'Length unit', 'Elements',
               'Body geometry', 'Coverage %', 'CRS', 'Ref latitude',
               'Local centre X', 'Local centre Y', 'World E', 'World N',
               'Georeferencing', 'MapConv E', 'MapConv N', 'MapConv H',
               'Grid rotation', 'Scale')]
    for r in res:
        mc = r['map_conversion'] or {}
        c = r['local_centre_m'] or [None, None, None]
        wc = r['world_centre_ENH'] or [None, None, None]
        cov = (100.0 * r['n_with_body_geometry'] / r['n_elements']) if r['n_elements'] else None
        s2.append([lab[r['file']], r['file'], r['schema'], r['length_unit'],
                   r['n_elements'], r['n_with_body_geometry'],
                   (round(cov, 1) if cov is not None else None,
                    S_FIX if cov is not None and cov < opt.min_geometry * 100 else S_PLAIN),
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
                   'Re-export with a real IfcMapConversion' if lvl < 50 else 'OK'])
    advice = georef_advice(res, lab)
    if advice:
        sg.append([])
        sg.append([('HOW TO FIX', S_SUB)])
        for line in advice:
            sg.append([line])

    sheets = [('Summary', s1, head_row), ('Models', s2, 1),
              ('Georeferencing', sg, 1), ('Duplicates', s3, 1)]

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
        s6 = [_hdr('Model', 'Element', 'IFC class', 'Type / family',
                   'Distance in plan (m)', 'Distance vertical (m)', 'Why flagged')]
        for r in res:
            for fl in r['floating']:
                s6.append([lab[r['file']], '#%d' % fl['id'], ifc_name(fl['class']),
                           fl['type'], fl['plan_m'], fl['vert_m'], fl['reason']])
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
    ap.add_argument('--min-geometry', type=float, default=0.90,
                    help='flag a model whose resolved-geometry share falls below '
                         'this fraction (default 0.90)')
    ap.add_argument('--max-rows', type=int, default=20,
                    help='max rows printed per section per model (default 20)')
    opt = ap.parse_args()

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
    for f in files:
        sys.stderr.write('reading %s ...\n' % os.path.basename(f))
        res.append(audit_file(f, opt))
    report(res, opt)

    if opt.json:
        with open(opt.json, 'w', encoding='utf-8') as fh:
            json.dump(res, fh, indent=1, default=str)
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
