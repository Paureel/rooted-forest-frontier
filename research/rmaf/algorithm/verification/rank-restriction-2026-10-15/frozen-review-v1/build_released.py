#!/usr/bin/env python3
"""Fresh source-only builds; author receipts select released bytes, not proof acceptance."""
import importlib.util,json,re,hashlib,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('fresh_replay',HERE/'released_replay.py');a=importlib.util.module_from_spec(spec);spec.loader.exec_module(a)
a.OUT=a.RMAF/'results/algorithm-rank-restriction-fresh-source-rebuild-v1.json'
a.state={'phase':'RELEASED-SOURCE-ONLY','runs':[],'audits':{},'bindings':{},'adapters':[]}
root=a.ROOT
assert json.loads((a.RMAF/'results/algorithm-rank-restriction-fresh-lean-gates-v1.json').read_text())['verdict']=='OWN-PREREGISTERED-LEAN-GATES-PASSED-BEFORE-CANDIDATE-POSITIVES'
def resolve(p):
 q=root/p
 if not q.exists():q=a.RMAF/p
 assert q.is_file(),p
 return q
def copy(p,folder,name,want):
 p=resolve(p);assert a.digest(p)==want,(str(p),want)
 q=folder/(name+'.lean');assert not q.exists();q.write_bytes(p.read_bytes());assert a.digest(q)==want
 return {'origin':str(p.relative_to(root)),'destination':str(q.relative_to(root)),'sha256':want}
def dag(folder,names):
 seen=set();order=[]
 def visit(n):
  if n in seen:return
  seen.add(n)
  for line in (folder/(n+'.lean')).read_text().splitlines():
   m=re.match(r'^import\s+(\w+)\s*$',line)
   if m and m[1] in names:visit(m[1])
  order.append(n)
 for n in names:visit(n)
 assert len(order)==len(names)
 return order
def go():
 for kind in ['rank','restriction']:
  folder=a.BUILD/kind;assert not folder.exists();folder.mkdir()
  if kind=='rank':
   manifest=resolve('research/rmaf/algorithm/universal233/rank_dichotomy/RANK-MANIFEST-v1.json');m=json.loads(manifest.read_text());receipt=resolve(m['canonical_receipt']);r=json.loads(receipt.read_text());names=[];bindings=[]
   for row in r['source_inputs']:
    name=row['compiled_module'];names.append(name)
    # Both exact originating bytes and actual frozen compile bytes are checked.
    origin=resolve(row['source']);assert a.digest(origin)==row['source_sha256']
    staged=receipt.parent/(name+'.lean');assert a.digest(staged)==row['compiled_sha256']
    b=copy(str(staged.relative_to(root)),folder,name,row['compiled_sha256']);b.update({'claimed_origin':row['source'],'origin_sha256':row['source_sha256'],'adapter':row['adapter'],'body_equal_to_origin':staged.read_bytes()==origin.read_bytes()});bindings.append(b)
    if row['adapter']:a.state['adapters'].append(b)
   expected=r['module_counts']
  else:
   manifest=resolve('research/rmaf/algorithm/universal233/restriction_bridge/RESTRICTION-MANIFEST-v1.json');m=json.loads(manifest.read_text());receipt=resolve(m['canonical_receipt']);r=json.loads(receipt.read_text());bindings=[];names=[]
   for p,h in m['dependency_source_hashes'].items():
    name=Path(p).stem;names.append(name);bindings.append(copy(p,folder,name,h))
   positives={'Restriction','Embedding','Partition','Cost','Forward','Reconstruction','Controls','Consumers'}
   for row in m['immutable_files']:
    p=Path(row['path']);name=p.stem
    if p.suffix=='.lean' and name in positives:names.append(name);bindings.append(copy(str(p),folder,name,row['sha256']))
   expected=r['module_origin_counts']
  a.state['bindings'][kind]=bindings;order=dag(folder,names);a.state[kind+'_order']=order;a.save()
  for name in order:a.compile_one(folder,name)
  audit=a.audit(folder,'FreshOriginAudit',names,names)
  assert audit['counts']==expected,(kind,audit['counts'],expected)
  a.state[kind+'_observed_axioms']=sorted({v for d in audit['all_declarations'] for v in d['axioms']})
  assert a.state[kind+'_observed_axioms']==['Classical.choice','Quot.sound','propext']
  a.save()
 a.state['verdict']='SOURCE-ONLY-BUILDS-AND-COMPLETE-ORIGIN-AUDITS-PASSED';a.save()
if __name__=='__main__':
 try:go()
 except Exception as e:a.state['verdict']='OPEN-SOURCE-REPLAY-FAILURE';a.state['error']=repr(e);a.save();raise
