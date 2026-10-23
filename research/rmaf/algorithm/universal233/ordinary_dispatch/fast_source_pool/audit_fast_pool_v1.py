# One-shot actual-root audit. Reuse records only for byte-identical frozen binaries.
from pathlib import Path
import ast,datetime,gzip,hashlib,importlib.util,json,os,re,resource,selectors,shlex,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/'results/algorithm-universal233-fast-source-pool-20261015T194053203759Z';V=D.parent/'resume_20261015T1810Z/compressed_pool_resume_v3.py';P=R/'results/algorithm-universal233-ordinary-source-pool-20261015T144445575127Z'
O=R/'results'/('algorithm-universal233-fast-source-audit-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
def load(n,p):
 spec=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
A=load('fast_actual_split_audit',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py');G=load('fast_actual_value_gate',D.parent/'producer_compatibility/compatibility.py')
wanted={'sha','string_sha','pin','margin','cap','run','source','header_source','parse_header','extract','read_rows','fingerprint'};parts=[n for n in ast.parse(V.read_text()).body if isinstance(n,ast.FunctionDef) and n.name in wanted];assert {n.name for n in parts}==wanted
exec(compile(ast.Module(body=parts,type_ignores=[]),str(V),'exec'),globals())
rec=dict(status='FRESH_ACTUAL_ROOT_CONTROLS',all_main_milestones='OPEN',full_faster_solver=False,runtime_claim=False,independent_acceptance=False,runs=[],inputs={},controls={},reused_producers=[],new_producers=[],sources=[])
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
for p in [Path(__file__),V,Path(A.__file__),Path(G.__file__),D/'TARGET-v1.md',B/'certificate.json',B/'extension-v1/certificate.json']:rec['inputs'][str(p.relative_to(R))]=sha(p)
(O/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes());save()
try:
 oldmanifest=D.parent/'resume_20261015T1810Z/pool_release_v1/SOURCE-POOL-MANIFEST-v1.json';assert sha(oldmanifest)=='64974e3b4358e87886466e409abf08d3982f1715b1504ae601e26a86aa7cc378';rec['inputs'][str(oldmanifest.relative_to(R))]=sha(oldmanifest)
 oldcert=R/'results/algorithm-universal233-ordinary-source-pool-compressed-20261015T182814513546Z/certificate.json';assert sha(oldcert)=='59874c67a59b6ed07d19ac728c4759b4835d4cc4cdac6ac89e4e03af90ab96ec';old=json.loads(oldcert.read_text());assert old['status']=='PASS_AUTHOR_COMPRESSED_POOL_AUDIT' and old['inputs'][str(V.relative_to(R))]==sha(V);rec['exact_generator_control_origin']=dict(path=str(oldcert.relative_to(R)),sha256=sha(oldcert))
 for n in ['actual_proof_body_reference_walk','opaque_bad_LR','opaque_bad_RL','clean_opaque','false_proof','production_pin_corruption']:assert n in old['controls']
 rec['controls']['exact_generator']=old['controls'];save()
 def nonproof(rr):
  for z in rr:
   if z['kind'] in {'definition','opaque'}:assert z['has_body'] and z['body'] and z.get('body_text_scope','FULL_NONPROOF_BODY')=='FULL_NONPROOF_BODY',('UNRESOLVED_NONPROOF_VALUE',z['actual_name'])
 # Fresh precise missing opaque body control, alongside a real full-body clean twin.
 sample=[dict(kind='opaque',actual_name='PlantedOpaque',has_body=True,body='Nat.zero',body_text_scope='FULL_NONPROOF_BODY')];nonproof(sample)
 for key,value in [('has_body',False),('body',''),('body_text_scope','OMITTED_THEOREM_PROOF_TEXT')]:
  try:nonproof([dict(sample[0],**{key:value})])
  except AssertionError:rec['controls']['opaque_'+key+'_corruption']='CAUGHT'
  else:raise AssertionError('MISSING_OPAQUE_BODY_ACCEPTED')
 T=O/'controls';T.mkdir();(T/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes());(T/'TrueControl.lean').write_text('import Std\nexample : (2:Nat)+3=5 := by decide\n');run(T,'TrueControl',T)
 (T/'FalseControl.lean').write_text('import Std\nexample : (2:Nat)+3=6 := by decide\n');out=run(T,'FalseControl',T,want=1);assert 'decide' in out and 'sorry' not in out;rec['controls']['fresh_kernel_false']='REJECTED';save()
 entries=json.loads((B/'extension-v1/certificate.json').read_text())['source_entries'];names=[e['module'] for e in entries]+['FastImports','FastConsumersV2'];assert len(names)==len(set(names))==382;pins={}
 for n in names:
  p=B/(n+'.lean');o=B/(n+'.olean');pins[str(p.relative_to(R))]=sha(p);pins[str(o.relative_to(R))]=sha(o);rec['sources'].append(dict(module=n,source_sha256=sha(p),olean_sha256=sha(o)))
 for e in entries:assert sha(B/(e['module']+'.lean'))==e['sha256']
 (O/'BUILD-PINS.json').write_text(json.dumps(pins,indent=2)+'\n');(O/'FreshHeader.lean').write_text(header_source(names));log=run(O,'FreshHeader',B);counts,expected=parse_header(log,names,B)
 for label,bad in [('foreign_path',log.replace(str(B/'RMAF.olean'),'/tmp/foreign/RMAF.olean',1)),('missing_path',re.sub(r'^PATH\|RMAF\|.*\n','',log,flags=re.M))]:
  try:parse_header(bad,names,B)
  except AssertionError:rec['controls'][label]='CAUGHT'
  else:raise AssertionError('ACTUAL_HEADER_CORRUPTION_ACCEPTED')
 rows=[];fresh=[];oldrows={e['module']:e for e in old['saved_producers']+old['new_producers']};oldpins=json.loads((R/'results/algorithm-universal233-ordinary-source-pool-resume-20261015T181255871989Z/OLD-BUILD-PINS.json').read_text())
 def check(n,c,rr):
  A.parse_producer(c,rr);assert [(z['index'],z['actual_name'],z['kind']) for z in rr]==expected[n],('ACTUAL_HEADER_MISMATCH',n);nonproof(rr)
 for n in names:
  po=P/(n+'.olean');pn=P/(n+'.lean');k=str(po.relative_to(R))
  if n not in oldrows or k not in oldpins or not po.exists() or sha(po)!=sha(B/(n+'.olean')):fresh.append(n);continue
  assert sha(po)==oldpins[k] and sha(pn)==pins[str((B/(n+'.lean')).relative_to(R))]
  e=oldrows[n];p=R/e['path'];assert sha(p)==e['sha256'];rr=read_rows(p);check(n,dict(producer=n,count=counts[n]),rr);rows+=fingerprint(rr);rec['reused_producers'].append(dict(module=n,path=e['path'],sha256=e['sha256'],actual_binary_sha256=sha(po),stored_occurrences=len(rr)));del rr
 # Fresh full-path row-loss/duplication controls for merger.
 e=rec['reused_producers'][0];rr=read_rows(R/e['path']);c=dict(producer=e['module'],count=counts[e['module']]);A.parse_producer(c,rr)
 for label,bad in [('missing',rr[:-1]),('duplicate',rr+[rr[0]])]:
  try:A.parse_producer(c,bad)
  except AssertionError:rec['controls']['actual_merge_'+label]='CAUGHT'
  else:raise AssertionError('ROW_CORRUPTION_ACCEPTED')
 rec.update(status='FRESH_DIFFERENT_BINARY_PRODUCER_AUDIT',missing_modules=fresh);save();print('EXACT_BINARY_REUSE',len(rec['reused_producers']),'FRESH',len(fresh),flush=True)
 # First shard is the measured pilot. Steady-state shard times are retained; 60s hardcap each.
 total=0
 for start in range(0,len(fresh),10):
  margin();shard=fresh[start:start+10];idx,folder=extract(O,names,shard,B,'Actual'+str(start//10));assert not idx['rejects']
  for c in idx['producer_counts']:
   n=c['producer'];p=folder/c['file'];total+=p.stat().st_size;assert total<768*(1<<20),'TOTAL_COMPRESSED_OUTPUT_CAP';rr=read_rows(p);check(n,c,rr);rows+=fingerprint(rr);rec['new_producers'].append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),compressed_bytes=p.stat().st_size,stored_occurrences=len(rr)));del rr
  save();print('FRESH_PRODUCERS',len(rec['new_producers']),'OF',len(fresh),'COMPRESSED_BYTES',total,flush=True)
 assert len(rec['reused_producers'])+len(rec['new_producers'])==382
 compat=G.inspect(rows);(O/'PRODUCER-COMPATIBILITY.json').write_text(json.dumps(compat,indent=2)+'\n');assert not compat['rejects'],compat['rejects'];ax=sorted({a for r in rows for a in r['axiom_references']});assert set(ax)<=A.ALLOWED
 for p,h in pins.items():assert sha(R/p)==h,'ACTUAL_BUILD_CHANGED'
 for p,h in rec['inputs'].items():assert sha(R/p)==h,'INPUT_CHANGED'
 rec.update(status='PASS_AUTHOR_FAST_CONSUMER_ONE_ROOT_SOURCE_PRODUCER_AUDIT',source_modules=380,master_modules=2,stored_producer_occurrences=len(rows),unique_names=len({r['actual_name'] for r in rows}),axiom_union=ax,duplicate_groups=len(compat['duplicates']),compressed_bytes=total,scope='380 fresh source builds plus two actual master imports. Stored rows reused only for byte-identical canonical .olean and .lean; all different binaries freshly extracted. Actual full proof references walked; theorem proof text may be omitted. Every nonproof definition and opaque value has retained nonempty full body. Finite selected-root compatibility only; main complete faster dispatcher and source/bit/payload recurrence OPEN.');save();print(rec['status'],len(rows),flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-AUDIT-v1.json').write_text(json.dumps(dict(directory=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n')
