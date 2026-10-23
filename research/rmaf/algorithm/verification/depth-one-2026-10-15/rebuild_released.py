#!/usr/bin/env python3
"""Source-only exact released depth01 replay; reuses own frozen Std detector API.
Author replay/checker code is never imported or executed.
"""
from pathlib import Path
import json,hashlib,importlib.util,re
H=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('own_frozen_std_api',H/'frozen-ready-v1/std_toy_gates.py');a=importlib.util.module_from_spec(sp);sp.loader.exec_module(a)
a.F=H/'isolated-release-v1';assert not a.F.exists();a.F.mkdir();a.OUT=a.ROOT/'research/rmaf/results/algorithm-depth-one-fresh-source-rebuild-v1.json';a.state={'phase':'RELEASED','runs':[],'audits':{},'bindings':[],'all_main_milestones':'OPEN','author_runners_executed':0,'scientific_oleans_copied':0}
mp=a.ROOT/'research/rmaf/algorithm/universal233/depth_one/DEPTH-ONE-MANIFEST-v1.json';manifest=json.loads(mp.read_text());rp=a.ROOT/manifest['canonical_receipt'];receipt=json.loads(rp.read_text());mods=list(receipt['module_origin_counts'])
std=json.loads((a.ROOT/'research/rmaf/results/algorithm-depth-one-fresh-std-gates-v1.json').read_text());assert std['verdict']=='PASS-BLIND-STD-TOY-FALSE-CUSTOM-PRIVATE-IMPORT-AND-INVENTORY-GATES'
try:
 bindings={}
 for source,want in receipt['input_hashes'].items():
  p=Path(source)
  if p.suffix=='.lean' and p.stem in mods:
   frozen=rp.parent/p.name;assert a.sha(frozen)==want,(source,'staged pin')
   origin=a.ROOT/p;current_match=a.sha(origin)==want
   q=a.F/p.name;q.write_bytes(frozen.read_bytes());assert a.sha(q)==want
   bindings[p.stem]={'module':p.stem,'frozen_source':str(frozen.relative_to(a.ROOT)),'frozen_source_sha256':want,'claimed_origin':source,'current_origin_hash_match':current_match,'adapter':None,'copied_olean':False}
 assert set(bindings)==set(mods)
 # Derive import order from the actual isolated source texts, rather than executing author tooling.
 seen=set();order=[]
 def visit(n):
  if n in seen:return
  seen.add(n)
  for line in (a.F/(n+'.lean')).read_text().splitlines():
   m=re.match(r'^import\s+(\w+)\s*$',line)
   if m and m[1] in mods:visit(m[1])
  order.append(n)
 for n in mods:visit(n)
 a.state['bindings']=list(bindings.values());a.state['order']=order;a.state['expected_author_origin_counts']=receipt['module_origin_counts'];a.save()
 for n in order:a.compile(n)
 rows=a.audit('FreshOriginAudit',mods,mods)
 assert len(rows)==2041 and not any(r['rejected'] for r in rows)
 a.state['origin_counts_equal_canonical']=a.state['audits']['FreshOriginAudit']['counts']==receipt['module_origin_counts']
 a.state['observed_axioms']=sorted({x for r in rows for x in r['axioms']});assert a.state['observed_axioms']==['Classical.choice','Quot.sound','propext']
 a.state['verdict']='PASS-ISOLATED-SOURCE-ONLY-DEPTH01-REBUILD-AND-COMPLETE-ORIGIN-AUDIT';a.save();print(json.dumps({'verdict':a.state['verdict'],'origins':len(mods),'declarations':len(rows),'counts_match':a.state['origin_counts_equal_canonical']}))
except Exception as e:a.state['verdict']='OPEN-SOURCE-REBUILD-FAILURE';a.state['error']=repr(e);a.save();raise
