ifc_audit.py - openBIM / IFC model-package review tool.

Checks a folder (or list) of .ifc files for:
  * Geolocation: schema, units, true north, world origin, IfcSite RefLat/Long/Elev,
    IfcMapConversion + IfcProjectedCRS, and the resolved real-world position of the model.
  * Duplicate elements: duplicate GlobalIds (validity error) and coincident
    duplicates (same type + name + placement).
  * Floating elements: physical elements far outside the model envelope.
  * Cross-file consistency: schema mix, CRS-declaration mix, and whether the
    models cluster to one location when federated.

Assumes standard one-entity-per-line STEP encoding (Revit, ArchiCAD, Tekla,
Civil3D, etc. all export this way). Placement resolution sums IfcLocalPlacement
translations (rotation ignored - adequate for gross position / outlier checks).

Usage:
  python ifc_audit.py                                    # audit the current folder
  python ifc_audit.py <folder-with-ifc-files>            # audit a package
  python ifc_audit.py model1.ifc model2.ifc ...          # audit specific files
  python ifc_audit.py <folder> --json report.json        # also dump raw JSON
  python ifc_audit.py <folder> --float-z 50 --float-xy 2 # tune float thresholds
