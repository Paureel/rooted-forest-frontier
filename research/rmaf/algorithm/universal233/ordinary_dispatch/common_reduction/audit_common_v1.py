#!/usr/bin/env python3
"""One-shot reuse of exact v3 extractor/sink functions, source-bound local IH.
No independent credit. Theorem proof TEXT omitted, actual proof references
traversed; nonproof definition and opaque bodies fully recorded.
"""
from pathlib import Path
import ast,datetime,gzip,hashlib,importlib.util,json,os,re,resource,selectors,shlex,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5]
B=R/'results/algorithm-universal233-ordinary-common-reduction-20261015T185752074314Z'
O=R/'results'/('algorithm-universal233-ordinary-common-reduction-compressed-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
V=D.parent/'resume_20261015T1810Z/compressed_pool_resume_v3.py'
def load(name,p):
 s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
A=load('local_exact_split_detector',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py')
C=load('local_exact_reference_detector',R/'research/rmaf/algorithm/universal233/rule5_case322/audit.py')
G=load('local_exact_value_gate',D.parent/'producer_compatibility/compatibility.py')
# Exact pinned completed function reuse without executing the other run's driver.
tree=ast.parse(V.read_text());wanted={'sha','string_sha','pin','margin','cap','run','source','header_source','parse_header','extract','read_rows','fingerprint'}
selected=[x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name in wanted];assert {x.name for x in selected}==wanted
exec(compile(ast.fix_missing_locations(ast.Module(body=selected,type_ignores=[])),str(V),'exec'),globals())
rec=dict(status='SOURCE_BOUND_AUDIT_RUNNING',all_main_milestones='OPEN',independent_acceptance=False,runtime_claim=False,source_work_claim=False,full_ordinary_solver=False,runs=[],controls={},inputs={})
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
for p in [Path(__file__),V,D.parent/'resume_20261015T1810Z/PROOF-TEXT-SCOPE-v3.md',B/'final-source-receipt-v1.json',B/'development-controls-v1.json',Path(A.__file__),Path(C.__file__),Path(G.__file__)]:rec['inputs'][str(p.relative_to(R))]=sha(p)
save();(O/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
try:
 # Reuse only actually passed preconstruction receipts of this exact generator.
 pool_dirs=sorted((R/'results').glob('algorithm-universal233-ordinary-source-pool-compressed-*'))
 candidates=[]
 for p in pool_dirs:
  q=p/'certificate.json'
  if q.exists():
   x=json.loads(q.read_text())
   if x.get('inputs',{}).get(str(V.relative_to(R)))==sha(V) and x.get('controls',{}).get('actual_proof_body_reference_walk')=='CAUGHT_WITH_FOREIGN_AXIOM_PRODUCER_EXCLUDED':candidates.append((q,x))
 assert candidates,'EXACT_MODIFIED_GENERATOR_FRESH_CONTROLS_NOT_AVAILABLE'
 q,controls=candidates[-1]
 for k in ['opaque_bad_LR','opaque_bad_RL','clean_opaque','actual_proof_body_reference_walk','production_pin_corruption','false_proof']:
  assert k in controls['controls'],k
 rec['fresh_controls_receipt']=dict(path=str(q.relative_to(R)),sha256=sha(q),scope='Passed exact-generator preconstruction controls only; other scientific result not imported as acceptance.')
 rec['controls']=controls['controls'];save()
 build=json.loads((B/'final-source-receipt-v1.json').read_text());assert build['status']=='PASS_AUTHOR_COMMON_SOURCE_CLOSURE_WITH_LITERAL_CONTROLS'
 controls=json.loads((B/'development-controls-v1.json').read_text());assert controls['status']=='PASS_AUTHOR_LITERAL_COMMON_CONTROLS'
 for e in controls['runs']:assert sha(D/(e['module']+'.lean'))==e['source_sha256']
 names=[x['module'] for x in build['source_entries']];assert len(names)==234
 pins={}
 for e in build['source_entries']:
  for suffix in ['lean','olean']:
   p=B/(e['module']+'.'+suffix);pins[str(p.relative_to(R))]=sha(p)
  assert sha(B/(e['module']+'.lean'))==e['sha256']
 (O/'BUILD-PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
 (O/'FreshHeader.lean').write_text(header_source(names));log=run(O,'FreshHeader',B);counts,expected=parse_header(log,names,B)
 idx,out=extract(O,names,names,B,'LocalIHAll');assert not idx['rejects'];rows=[]
 for count in idx['producer_counts']:
  p=out/count['file'];actual=read_rows(p);A.parse_producer(count,actual)
  assert [(r['index'],r['actual_name'],r['kind']) for r in actual]==expected[count['producer']]
  rows.extend(fingerprint(actual));del actual
 keys=['OrdinaryDispatch.commonFresh','OrdinaryDispatch.selected_common_ready','OrdinaryDispatch.runCommonCherry','OrdinaryDispatch.selected_common_label_decrease','OrdinaryDispatch.common_query_equivalence','OrdinaryDispatch.common_expansion_original','OrdinaryDispatch.selected_common_query_exact']
 for n in keys:assert any(r['actual_name']==n for r in rows),n
 compatibility=G.inspect(rows);assert not compatibility['rejects'];(O/'COMPATIBILITY.json').write_text(json.dumps(compatibility,indent=2)+'\n')
 for p,h in pins.items():assert sha(R/p)==h,'BUILD_CHANGED'
 for p,h in rec['inputs'].items():assert sha(R/p)==h,'INPUT_CHANGED'
 ax=sorted({a for r in rows for a in r['axiom_references']});assert set(ax)<=A.ALLOWED
 rec.update(status='PASS_AUTHOR_COMMON_REDUCTION_SOURCE_PRODUCER',source_builds=234,stored_producer_occurrences=len(rows),axiom_union=ax,interfaces=keys,theorem_proof_text='OMITTED in new JSON only; actual full proof references traversed; full proof binary .olean pinned. All nonproof opaque/definition value representations retained.',first_external_gap='Actual ordinary dispatch and per-query LocalOrdinaryIH from well-founded recursion, source applicability and total source/bit/payload recurrence remain OPEN.')
 save();(O/'VERDICT.txt').write_text(rec['status']+'\nNo runtime ghost, full ordinary solver or improved-base acceptance.\n');print(rec['status'],len(rows),flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-COMMON-COMPRESSED-v1.json').write_text(json.dumps(dict(directory=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n')
