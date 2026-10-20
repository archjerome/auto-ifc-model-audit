ifc_audit.py - openBIM / IFC model-package review tool. (v4)

Reads a folder of .ifc files and reports what a federated package gets wrong.
Pure Python 3 standard library: no pip install, no IFC toolkit, no add-in.

Every finding carries a stable rule id, so it can be cited in an email, a BEP,
or a comment back from the design team. `--rules` prints the table.

`--bcf` writes the same findings as a BCF 2.1 issue list, so each one opens
next to the element that caused it in Revit, Navisworks, Solibri or any other
BCF reader - with the explanation attached as a comment, and a topic GUID
derived from the finding so re-running the audit updates the issue list
instead of duplicating it.

What a given project, client or authority asks for is not built in - the tool
runs on projects in several countries, and any one region's requirements baked
into the source would be wrong for all the others. Those live in a profile
file instead; see below.

Checks
  * Spatial structure: IfcProject at the apex with IfcSite, IfcBuilding,
    IfcBuildingStorey and IfcSpace each aggregated into the one above it;
    every element contained in a storey, inheritance down a decomposition
    included; and the storeys of the package agreeing on name and level
    across the discipline models.
  * Export setup: the ViewDefinition (MVD) declared in the file header, graded
    against the schema actually written.
  * Classification: whether each element says what it is - an IfcClass that is
    not a generic proxy, and a PredefinedType that is neither NOTDEFINED nor
    pushed to USERDEFINED.
  * Geolocation: schema, units, true north, IfcSite RefLat/Long/Elev,
    IfcMapConversion + IfcProjectedCRS, LoGeoRef level, and the resolved
    real-world position of each model.
  * Duplicate elements: duplicate GlobalIds (a schema error) and geometric
    duplicates, graded by evidence. Elements that merely overlap are reported
    separately as interferences, never as duplicates.
  * Floating elements: physical elements anomalously far from the model, found
    with a median + MAD fence rather than a percentile envelope.
  * Cross-file consistency: schema mix, unit mix, CRS mix, whether the models
    share one real-world survey anchor, and whether they agree on the storeys.

Storey levels are compared in the survey datum - the storey placement plus
whatever height the model carries in IfcMapConversion - so a model exported on
shared coordinates, which puts the survey offset in the IfcSite placement, is
comparable with one exported on the survey point, which puts it in
IfcMapConversion. A same-named level differing between models by less than
`--storey-datum` is reported as a datum difference to confirm, finished floor
level against top of concrete, rather than as a fault.

Element extents come from the element's Body representation with full
placement matrices, rotation included, resolved through IfcLocalPlacement ->
IfcMappedItem -> IfcRepresentationMap -> solid. Length units are read from the
IfcProject's own IfcUnitAssignment, so millimetre, metre, foot and inch models
all work.

Assumes standard one-entity-per-line STEP encoding (Revit, ArchiCAD, Tekla and
Civil3D all export this way).

Usage
  python ifc_audit.py                                    # audit the current folder
  python ifc_audit.py <folder-with-ifc-files>            # audit a package
  python ifc_audit.py model1.ifc model2.ifc ...          # audit specific files
  python ifc_audit.py <folder> --excel audit.xlsx        # shareable workbook
  python ifc_audit.py <folder> --bcf audit.bcfzip        # BCF 2.1 issue list
  python ifc_audit.py <folder> --json report.json        # machine-readable
  python ifc_audit.py <folder> --clash                   # interference report
  python ifc_audit.py <folder> --profile project.json    # project expectations
  python ifc_audit.py --rules                            # print the rule table

Submission profiles
  A profile is a JSON file stating what one project is being held to - a
  national e-submission regime, a client EIR, a BEP, a JV modelling standard.
  It can set:

    options          the schema and MVD to expect, thresholds, tolerances.
                     Anything you pass on the command line yourself wins.
    severity_words   what to call the three grades, so the report reads beside
                     a checker that says FAIL / ALERT / PASS.
    checks           the external checklist being answered, each item mapped
                     onto the rule ids that address it.

  The checklist drives a PROFILE COVERAGE section listing every item, the
  rules behind it, and the grade each reached - including the items with no
  rule behind them, marked "not yet". Listing those is the point: a check that
  did not run must not read as a check that passed. A profile cannot claim
  coverage it has no rule for.

  `profiles/example.json` is a worked example. Keep real profiles with the
  project rather than in this repository - they are project data, revised on
  the project's schedule, and the next project needs a different one.

  This tool is a pre-check. Where a project is checked by someone else, their
  result is the one that counts; this finds the problems while they are still
  cheap to fix.

Handing the results over
  `--excel` is for the people who read and `--bcf` is for the people who model:
  the same findings under the same rule ids, one as a workbook with a sheet per
  area, the other as topics that open next to the element.

  A BCF topic carries the elements by IfcGuid, an orthogonal camera framed on
  them, a plan of the model with them marked on it, the instance detail as the
  description and the rule's own statement as the first comment. Only FIX and
  REVIEW become topics. `--bcf-max` caps how many are written, taken worst
  first and then a rule at a time so one noisy rule cannot fill the file; what
  did not fit is counted and printed, because a topic that did not fit is not a
  finding that went away.

See Instructions.txt for setup, the full option list, and how each verdict is
reached.
