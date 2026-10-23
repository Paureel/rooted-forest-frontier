#!/usr/bin/env python3
"""Read actual request colors; compare their equality classes to frozen graph signatures.
Postrelease instrumentation only; all original fixtures and class expectations frozen.
"""
import importlib.util,json,sys
from pathlib import Path
H=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('own_readout_v2',H/'actual_readouts_v2.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
a=m.a;a.OUT=a.RMAF/'results/algorithm-rank-restriction-fresh-canonical-colors-v1.json';a.state={'runs':[],'audits':{},'comparisons':[],'scope':'Actual frozen localColor equality classes and raw program; original fixtures/expectations remain unchanged'}
lines=[m.rankhead+'\nopen Universal233.Assembly Universal233.VertexGeometry\n'];wants={}
for f in m.clear['cases']:
 T=m.tree(f['T']);S=m.tree(f['S']);labels=sorted(m.m.g.Original(f['T']).labels)
 vs=['['+','.join('true' if c=='1' else 'false' for c in v)+']' for v in f['requested_vertices']]
 req='(.at '+vs[0]+')' if len(vs)==1 else '(.both '+vs[0]+' '+vs[1]+')';col='(localColor '+T+' '+req+')';ls=m.natlist(labels);cols=dict(f['colors'])
 ids=f['id'];wants[ids+'/classes']=[[cols[x]==cols[y] for y in labels] for x in labels];expr=ls+'.map (fun x => '+ls+'.map (fun y => '+col+' x == '+col+' y))'
 lines.append('#eval emit '+json.dumps(ids+'/classes')+' (Lean.toJson ('+expr+'))')
 wants[ids+'/rank']=len(set(cols.values()));lines.append('#eval emit '+json.dumps(ids+'/rank')+' (Lean.toJson (inputRank '+S+' '+col+'))')
 wants[ids+'/receipt']=m.outrec(m.m.generate(f['S'],cols,f['budget']));lines.append('#eval emit '+json.dumps(ids+'/receipt')+' (rj (generate '+S+' '+col+' '+str(f['budget'])+'))')
 wants[ids+'/internal_guard']=[True]*len(vs);lines.append('#eval emit '+json.dumps(ids+'/internal_guard')+' (Lean.toJson ('+'['+','.join('!((leafList (leaves '+T+') '+T+').contains '+v+')' for v in vs)+']'+'))')
# Literal singleton-root label is selected, so request nonlabel-root guard fails.
wants['singleton_root_is_nonlabel']=False;lines.append('#eval emit "singleton_root_is_nonlabel" (Lean.toJson (!((leafList [7] (.leaf 7)).contains [])))')
folder=a.BUILD/'rank';name='FreshCanonicalColorReadout';(folder/(name+'.lean')).write_text('\n'.join(lines)+'\n')
try:
 log=a.compile_one(folder,name);seen={}
 for l in log.splitlines():
  if l.startswith('READOUT|'):
   _,id,v=l.split('|',2);seen[id]=json.loads(v)
 assert set(seen)==set(wants)
 for id,w in wants.items():
  ok=seen[id]==w;a.state['comparisons'].append({'id':id,'actual':seen[id],'expected':w,'passed':ok});a.save();assert ok,id
 a.state['verdict']='PASS-ACTUAL-CANONICAL-REGION-AND-JOINT-COLOR-CLASSES-RAW-OUTPUTS-AND-ROOT-GUARDS';a.state['extra_replications']=0;a.save();print(a.state['verdict'])
except Exception as e:a.state['verdict']='OPEN-CANONICAL-COLOR-READOUT-FAILURE';a.state['error']=repr(e);a.save();raise
