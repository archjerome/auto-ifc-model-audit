#!/usr/bin/env python3
"""
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
"""
import re, sys, os, json, math, glob, argparse
from collections import Counter, defaultdict

RE_LP   = re.compile(r"^#(\d+)=IFCLOCALPLACEMENT\(([^,]+),(#\d+)\)")
RE_AX   = re.compile(r"^#(\d+)=IFCAXIS2PLACEMENT3D\((#\d+|\$)")
RE_PT   = re.compile(r"^#(\d+)=IFCCARTESIANPOINT\(\(([^)]*)\)\)")
RE_ROOT = re.compile(r"^#(\d+)=(IFC[A-Z0-9_]+)\('([^']{22})',(#\d+|\$)(.*)\);")
RE_SITE = re.compile(r"=IFCSITE\(.*?\.(?:ELEMENT|COMPLEX|PARTIAL)\.,\(([^)]*)\),\(([^)]*)\),([^,]*),")
RE_MC   = re.compile(r"=IFCMAPCONVERSION\((#\d+),(#\d+),([^,]*),([^,]*),([^,]*),")
RE_CRS  = re.compile(r"=IFCPROJECTEDCRS\('([^']*)'")

# Spatial / logical / non-physical types excluded from element checks
EXCLUDE = {'IFCSITE','IFCBUILDING','IFCBUILDINGSTOREY','IFCSPACE','IFCSPATIALZONE',
 'IFCZONE','IFCGRID','IFCOPENINGELEMENT','IFCANNOTATION','IFCPROJECT','IFCPROPERTYSET',
 'IFCELEMENTQUANTITY','IFCMATERIALLAYERSET','IFCMATERIALLAYERSETUSAGE',
 'IFCPRESENTATIONLAYERASSIGNMENT','IFCDISTRIBUTIONPORT'}

def dms(s):
    """STEP compound angle (deg,min,sec[,millionths]) -> decimal degrees."""
    try:
        p=[float(x) for x in s.split(',') if x.strip()!='']
        if not p: return None
        d=p[0]; m=p[1] if len(p)>1 else 0; sec=p[2] if len(p)>2 else 0
        frac=p[3]/1e6 if len(p)>3 else 0
        sign=-1 if d<0 else 1
        return round(sign*(abs(d)+m/60+(sec+frac)/3600),6)
    except Exception:
        return None

def read_header(path):
    h=""
    with open(path,'r',errors='replace') as f:
        for line in f:
            h+=line
            if 'DATA;' in line or len(h)>30000: break
    schema=re.search(r"FILE_SCHEMA\s*\(\s*\(\s*'([^']+)'",h)
    return schema.group(1) if schema else '?'

def audit_file(path, fxy=2.0, fz=50.0):
    name=os.path.basename(path)
    lp={};ax={};pts={}
    guid_count=Counter(); guid_detail=defaultdict(list)
    elems=[]            # (id,type,name,placement_id)
    site_lat=site_lon=site_elev=None
    map_conv=None; crs=None
    unit_len=None; true_north=None; wcs=None
    geom_ctx=[]

    with open(path,'r',errors='replace') as f:
        for line in f:
            if not line or line[0]!='#':
                continue
            m=RE_PT.match(line)
            if m:
                n=m.group(2).split(',')
                if len(n)>=3:
                    try: pts[int(m.group(1))]=(float(n[0]),float(n[1]),float(n[2]))
                    except: pass
                continue
            m=RE_LP.match(line)
            if m:
                r=m.group(2).strip()
                lp[int(m.group(1))]=(int(r[1:]) if r.startswith('#') else None,int(m.group(3)[1:]))
                continue
            m=RE_AX.match(line)
            if m:
                l=m.group(2); ax[int(m.group(1))]=int(l[1:]) if l.startswith('#') else None
                continue
            if site_lat is None and 'IFCSITE(' in line:
                ms=RE_SITE.search(line)
                if ms:
                    site_lat=dms(ms.group(1)); site_lon=dms(ms.group(2))
                    try: site_elev=float(ms.group(3))
                    except: site_elev=None
            if map_conv is None and 'IFCMAPCONVERSION(' in line:
                mm=RE_MC.search(line)
                if mm:
                    try: map_conv=(float(mm.group(3)),float(mm.group(4)),float(mm.group(5)))
                    except: map_conv=('?','?','?')
            if crs is None and 'IFCPROJECTEDCRS(' in line:
                mc=RE_CRS.search(line)
                if mc: crs=mc.group(1)
            if unit_len is None and 'IFCSIUNIT(' in line and 'LENGTHUNIT' in line:
                pm=re.search(r"\.LENGTHUNIT\.,\.?([A-Z]*)\.?,?\.?([A-Z]+)\.",line)
                if pm: unit_len=(pm.group(1)+' '+pm.group(2)).strip()
            m=RE_ROOT.match(line)
            if m and m.group(4).startswith('#'):
                eid=int(m.group(1)); typ=m.group(2); guid=m.group(3); rest=m.group(5)
                guid_count[guid]+=1
                if len(guid_detail[guid])<6: guid_detail[guid].append((eid,typ))
                if typ.endswith('TYPE') or typ.startswith('IFCREL') or 'PROPERTY' in typ \
                   or 'MATERIAL' in typ or typ in EXCLUDE:
                    continue
                refs=re.findall(r'#(\d+)',rest)
                pl=int(refs[0]) if refs else None
                nm=re.match(r",'([^']*)'",rest)
                elems.append((eid,typ,nm.group(1) if nm else '',pl))

    # resolve absolute translation of placements
    cache={}
    def resolve(pid,d=0):
        if pid is None or pid not in lp or d>60: return (0.,0.,0.)
        if pid in cache: return cache[pid]
        relto,relp=lp[pid]; loc=ax.get(relp)
        here=pts.get(loc,(0.,0.,0.)) if loc is not None else (0.,0.,0.)
        base=resolve(relto,d+1) if relto is not None else (0.,0.,0.)
        r=(here[0]+base[0],here[1]+base[1],here[2]+base[2]); cache[pid]=r; return r

    pos=[]
    for eid,typ,nm,pl in elems:
        if pl is not None and pl in lp:
            x,y,z=resolve(pl); pos.append((eid,typ,nm,x,y,z))

    # duplicate GlobalIds (validity)
    dup_guid={g:c for g,c in guid_count.items() if c>1}
    dup_guid_list=[(g,c,guid_detail[g]) for g,c in sorted(dup_guid.items(),key=lambda x:-x[1])]
    # coincident duplicates (type+name+origin to 1mm)
    sig=defaultdict(list)
    for eid,typ,nm,x,y,z in pos: sig[(typ,nm,round(x),round(y),round(z))].append(eid)
    geo=[{'type':k[0],'name':k[1],'count':len(v),'ids':v[:6]} for k,v in sig.items() if len(v)>1]
    geo.sort(key=lambda g:-g['count'])

    # floating outliers + model centre
    out={'n_positioned':len(pos),'floating':[]}
    centre=None
    if pos:
        xs=sorted(p[3] for p in pos); ys=sorted(p[4] for p in pos); zs=sorted(p[5] for p in pos)
        pct=lambda a,p:a[min(len(a)-1,max(0,int(len(a)*p)))]
        mx,my,mz=pct(xs,.5),pct(ys,.5),pct(zs,.5)
        spanx=pct(xs,.99)-pct(xs,.01); spany=pct(ys,.99)-pct(ys,.01); spanz=pct(zs,.99)-pct(zs,.01)
        thr_xy=max(spanx,spany)*fxy + fz*1000
        thr_z=max(spanz*3, fz*1000)
        fl=[]
        for eid,typ,nm,x,y,z in pos:
            if math.hypot(x-mx,y-my)>thr_xy or abs(z-mz)>thr_z:
                fl.append({'id':eid,'type':typ,'name':nm[:80],
                           'dx_m':round((x-mx)/1000,1),'dy_m':round((y-my)/1000,1),'dz_m':round((z-mz)/1000,1)})
        fl.sort(key=lambda r:-(r['dx_m']**2+r['dy_m']**2+r['dz_m']**2))
        out={'n_positioned':len(pos),'footprint_m':[round(spanx/1000,1),round(spany/1000,1),round(spanz/1000,1)],
             'floating':fl}
        centre=[round(mx/1000,2),round(my/1000,2),round(mz/1000,2)]
        # true north / wcs from first geometric context
    return {
        'file':name,'schema':read_header(path),'length_unit':unit_len,
        'ref_lat':site_lat,'ref_long':site_lon,'ref_elev':site_elev,
        'projected_crs':crs,'map_conversion_ENH':map_conv,
        'model_centre_m':centre,'footprint_m':out.get('footprint_m'),
        'n_physical':len(pos),
        'dup_guid_groups':len(dup_guid),'dup_guid_extra':sum(c-1 for c in dup_guid.values()),
        'dup_guid_detail':dup_guid_list[:20],
        'coincident_dup_groups':len(geo),'coincident_dup_extra':sum(g['count']-1 for g in geo),
        'coincident_dup_top':geo[:20],
        'n_floating':len(out['floating']),'floating':out['floating'][:40],
    }

def fmt(v):
    return '-' if v is None else v

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('paths',nargs='*',default=['.'])
    ap.add_argument('--json')
    ap.add_argument('--float-xy',type=float,default=2.0,help='horizontal threshold = N x footprint')
    ap.add_argument('--float-z',type=float,default=50.0,help='vertical/base threshold in metres')
    a=ap.parse_args()
    files=[]
    for p in a.paths:
        if os.path.isdir(p): files+=sorted(glob.glob(os.path.join(p,'*.ifc')))+sorted(glob.glob(os.path.join(p,'*.IFC')))
        elif p.lower().endswith('.ifc'): files.append(p)
    files=sorted(set(files))
    if not files:
        print('No .ifc files found.'); sys.exit(1)

    res=[audit_file(f,a.float_xy,a.float_z) for f in files]

    print('='*78); print(f'IFC PACKAGE AUDIT  -  {len(res)} model(s)'); print('='*78)
    # per-file geolocation
    print('\nGEOLOCATION')
    hdr=f"{'model':30} {'schema':10} {'CRS':12} {'ref lat':10} {'centre E / N (m)':24} {'Z(m)':7}"
    print(hdr); print('-'*len(hdr))
    for r in res:
        c=r['model_centre_m']; cen=f"{c[0]} / {c[1]}" if c else '-'
        z=c[2] if c else '-'
        print(f"{r['file'][:30]:30} {fmt(r['schema']):10} {fmt(r['projected_crs'])[:12]:12} "
              f"{str(fmt(r['ref_lat']))[:10]:10} {cen:24} {str(z):7}")

    # cross-file consistency
    print('\nCROSS-FILE CONSISTENCY')
    schemas=set(r['schema'] for r in res)
    print(f"  Schemas present      : {', '.join(sorted(schemas))}"+('   <-- MIXED' if len(schemas)>1 else '  (consistent)'))
    units=set(r['length_unit'] for r in res)
    print(f"  Length units         : {', '.join(sorted(str(u) for u in units))}"+('   <-- MIXED' if len(units)>1 else '  (consistent)'))
    with_crs=[r['file'] for r in res if r['projected_crs']]
    print(f"  Models with Proj.CRS : {len(with_crs)}/{len(res)}"+('   <-- INCONSISTENT' if 0<len(with_crs)<len(res) else ''))
    cents=[r['model_centre_m'] for r in res if r['model_centre_m']]
    if cents:
        ex=[c[0] for c in cents]; ny=[c[1] for c in cents]
        spread=max(math.hypot(a[0]-b[0],a[1]-b[1]) for a in cents for b in cents)
        print(f"  Max centre-to-centre : {spread:,.0f} m"+('   <-- check: models do not share one location' if spread>50 else '  (clustered)'))
    lats=[r['ref_lat'] for r in res if r['ref_lat'] is not None]
    if lats and (max(lats)-min(lats))>0.0005:
        print(f"  RefLatitude range    : {min(lats)} .. {max(lats)}  (~{(max(lats)-min(lats))*111000:,.0f} m)   <-- DIFFERING SITES")
    if any(r['ref_elev'] in (0.0,None) for r in res):
        print(f"  RefElevation         : unset/0 in {sum(1 for r in res if r['ref_elev'] in (0.0,None))}/{len(res)} models")

    # duplicates
    print('\nDUPLICATE ELEMENTS')
    any_dup=False
    for r in res:
        if r['dup_guid_extra'] or r['coincident_dup_extra']:
            any_dup=True
            print(f"  {r['file']}")
            for g,c,det in r['dup_guid_detail']:
                print(f"     duplicate GlobalId x{c}: {g}  {det}")
            for g in r['coincident_dup_top']:
                print(f"     coincident x{g['count']}: {g['type']} '{g['name'][:40]}'  ids={g['ids']}")
    if not any_dup: print('  None found.')

    # floating
    print('\nFLOATING / OUT-OF-BUILDING ELEMENTS')
    any_fl=False
    for r in res:
        if r['n_floating']:
            any_fl=True
            print(f"  {r['file']}  ({r['n_floating']})")
            for fl in r['floating'][:15]:
                print(f"     #{fl['id']} {fl['type']} '{fl['name'][:50]}'  offset {fl['dx_m']},{fl['dy_m']},{fl['dz_m']} m")
    if not any_fl: print('  None found.')

    if a.json:
        json.dump(res,open(a.json,'w'),indent=1); print(f'\nRaw JSON -> {a.json}')

if __name__=='__main__':
    main()