#!/usr/bin/env python3
"""Source-only joint consuming seam; imports only renamed, all bodies/pins retained."""
import importlib.util,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('own_api',HERE/'released_replay.py');a=importlib.util.module_from_spec(s);s.loader.exec_module(a)
a.OUT=a.RMAF/'results/algorithm-rank-restriction-fresh-joint-consumer-v1.json';a.state={'runs':[],'audits':{},'adapters':[]}
old=json.loads((a.RMAF/'results/algorithm-rank-restriction-fresh-source-rebuild-v1.json').read_text());rankmods=old['rank_order'];resmods=old['restriction_order'];folder=a.BUILD/'joint';assert not folder.exists();folder.mkdir()
try:
 for n in rankmods:
  p=a.BUILD/'rank'/(n+'.lean');q=folder/p.name;q.write_bytes(p.read_bytes());assert a.digest(p)==a.digest(q)
 names={n:'Res'+n for n in resmods if n not in ['RMAF','Geometry','Bridge','Composition']}
 for n in resmods:
  p=a.BUILD/'restriction'/(n+'.lean')
  if n not in names:
   assert p.read_bytes()==(folder/p.name).read_bytes();continue
  original=p.read_text();copy=original
  for x,y in names.items():copy=re.sub(r'^import '+re.escape(x)+r'$', 'import '+y,copy,flags=re.M)
  q=folder/(names[n]+'.lean');q.write_text(copy)
  assert re.sub(r'^import .*$', '',original,flags=re.M)==re.sub(r'^import .*$', '',copy,flags=re.M)
  a.state['adapters'].append({'origin':str(p.relative_to(a.ROOT)),'origin_sha256':a.digest(p),'copy':str(q.relative_to(a.ROOT)),'copy_sha256':a.digest(q),'change':'module filename and import names only; every non-import character equal'})
 p=HERE/'ConsumerInterface.lean';(folder/p.name).write_bytes(p.read_bytes());order=rankmods+[names[n] for n in resmods if n in names]+['ConsumerInterface'];a.state['order']=order;a.save()
 for n in order:a.compile_one(folder,n)
 z=a.audit(folder,'FreshJointOriginAudit',['ConsumerInterface'],order)
 assert not z['bad']
 a.state['verdict']='PASS-GUARDED-ACTUAL-OUTPUT-FORWARD-REVERSE-AND-EXACT-COST-SEAM';a.state['source_edits']=0;a.state['added_reviewer_modules']=1;a.save();print(json.dumps({'status':a.state['verdict'],'origins':len(order),'declarations':z['total']}))
except Exception as e:a.state['verdict']='OPEN-JOINT-SEAM-FAILURE';a.state['error']=repr(e);a.save();raise
