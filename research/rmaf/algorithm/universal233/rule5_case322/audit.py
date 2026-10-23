#!/usr/bin/env python3
"""One-shot Case322 author audit wrapper, completed detector contact only.
Uses the frozen original source-producer instrument rather than forking it.
Fresh Std-only controls extend its coverage to both coalescence import orders.
"""
from pathlib import Path
import importlib.util,json,re
D=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('completed_rule5_audit',D.parent/'rule5_local/audit.py')
A=importlib.util.module_from_spec(sp);sp.loader.exec_module(A)
audit_source=A.audit_source;parse=A.parse;run_lean=A.run_lean;ALLOW=A.ALLOW

def detector_controls(out):
 fixtures={
 'C322CleanA':'import Std\ntheorem Case322DetectorShared : True := True.intro\n',
 'C322CleanB':'import Std\ntheorem Case322DetectorShared : True := True.intro\ntheorem Case322DetectorOwn : (2:Nat)+3=5 := by decide\n',
 'C322Hostile':'import Std\naxiom Case322DetectorShared : True\ntheorem Case322DetectorHostileOwn : (2:Nat)+3=5 := by decide\n',
 'C322Private':'import Std\nnamespace C322Hidden\nprivate axiom unused : False\nprivate theorem ownClean : True := True.intro\nend C322Hidden\n',
 'C322Unused':'import Std\naxiom Case322UnusedPublic : True\ntheorem Case322UnusedOwn : True := True.intro\n'}
 for name,src in fixtures.items():
  (out/(name+'.lean')).write_text(src);p=run_lean(out,name,True);assert p.returncode==0,(name,p.stdout)
 rec={};cleanlogs=[]
 for i,mods in enumerate([['C322CleanA','C322CleanB'],['C322CleanB','C322CleanA']]):
  name='C322CleanAudit'+str(i);(out/(name+'.lean')).write_text(audit_source(mods));p=run_lean(out,name)
  assert p.returncode==0,p.stdout
  rows,ss,paths=parse(p.stdout,mods,out);shared=[r for r in rows if r['name']=='Case322DetectorShared']
  assert len(shared)==2 and len({r['producer'] for r in shared})==2
  rec[name]=dict(imports=mods,occurrences=len(rows),shared_occurrences=len(shared));cleanlogs.append((p.stdout,mods,rows))
 for i,mods in enumerate([['C322CleanA','C322Hostile'],['C322Hostile','C322CleanA'],['C322Private'],['C322Unused']]):
  name='C322HostileAudit'+str(i);(out/(name+'.lean')).write_text(audit_source(mods));p=run_lean(out,name)
  assert p.returncode!=0 and 'REJECT_DIRECT_CUSTOM_AXIOM|' in p.stdout,(name,p.stdout)
  rec[name]=dict(imports=mods,direct_custom_axiom='CAUGHT')
 log,mods,rows=cleanlogs[0]
 for tag,bad in [('missing',re.sub(r'^PRODUCERJSON\|.*\n','',log,count=1,flags=re.M)),('duplicate',log+'PRODUCERJSON|'+json.dumps(rows[0])+'\n')]:
  try:parse(bad,mods,out)
  except AssertionError:rec[tag]='CAUGHT'
  else:raise AssertionError('CORRUPTION_SURVIVED|'+tag)
 return rec
