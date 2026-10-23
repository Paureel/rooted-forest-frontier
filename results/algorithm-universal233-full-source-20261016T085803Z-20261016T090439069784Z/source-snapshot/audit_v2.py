# One-shot exact consumer audit using the measured completed compressed engine.
# No dependency rebuild, independent credit, or full-runtime inference.
from pathlib import Path
import ast,datetime,gzip,hashlib,importlib.util,json,os,re,resource,selectors,shlex,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/json.loads((D/'BUILD-v1.json').read_text())['directory']
O=B/'author-audit-v2';assert not O.exists();O.mkdir();P=B/'author-audit-v1'
V=D.parent/'resume_20261015T1810Z/compressed_pool_resume_v3.py'
def load(n,p):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
A=load('fullsource_producer',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py')
G=load('fullsource_compatibility',D.parent/'producer_compatibility/compatibility.py')
class MemoryCap(ast.NodeTransformer):
 def visit_Call(self,n):
  self.generic_visit(n)
  if isinstance(n.func,ast.Attribute) and isinstance(n.func.value,ast.Name) and n.func.value.id=='subprocess' and n.func.attr=='Popen':n.args[0].left.left.elts.append(ast.Constant(value='--memory=3072'))
  return n
wanted={'sha','string_sha','pin','margin','cap','run','source','header_source','parse_header','extract','read_rows','fingerprint'}
for n in ast.parse(V.read_text()).body:
 if isinstance(n,ast.FunctionDef) and n.name in wanted:
  n=MemoryCap().visit(n);exec(compile(ast.fix_missing_locations(ast.Module(body=[n],type_ignores=[])),str(V),'exec'),globals())
compressed_source=source
full={'GeneralAgreementWork','WeightedOrdinaryWork','PrefixSourceWork','CommonConstructionWork','CommonAgreementConsumer','CommonBranchWork'}
def source(imports,modules,out):
 s=compressed_source(imports,modules,out)
 if not set(modules)<=full:return s
 a='let body := match ci with | .thmInfo _ => none | _ => ci.value? true';assert s.count(a)==1;s=s.replace(a,'let body := ci.value? true')
 a='match ci with | .thmInfo _ => "OMITTED_THEOREM_PROOF_TEXT" | _ => "FULL_NONPROOF_BODY"';assert s.count(a)==1;return s.replace(a,'"FULL_ALL_BODY"')
rec=dict(status='CHECKING',all_main_milestones='OPEN',full_runtime_claim=False,independent_acceptance=False,runs=[],inputs={},controls={},sources=[],reused_producers=[],new_producers=[],version_compatibility=[])
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
def metadata_compare(a,b):
 assert set(a)==set(b),'METADATA_NAME_SET'
 assert all(a[k]==b[k] for k in a),'FULL_CONSTANTINFO_DIFFERENCE'
def metadata_profile(root,n,label):
 name='Metadata'+label;output=O/(name+'.json')
 code='import '+n+'\nimport Lean\nopen Lean Elab Command\nrun_cmd do\n let env ← getEnv\n let wanted : Name := `'+n+'''\n let mut rows : Array Json := #[]
 for i in [:env.header.moduleNames.size] do
  if env.header.moduleNames[i]! == wanted then
   let data := env.header.moduleData[i]!
   for ci in data.constants do
    let kind := match ci with
     | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
     | .axiomInfo _ => "axiom" | .quotInfo _ => "quotient" | _ => "skip"
    unless kind == "skip" do
     rows := rows.push (Json.mkObj [("name",toJson ci.name.toString),("kind",toJson kind),("full_constant_info",toJson (reprStr ci))])
 liftIO <| IO.FS.writeFile '''+json.dumps(str(output))+''' (Json.arr rows).pretty
'''
 (O/(name+'.lean')).write_text(code);run(O,name,root)
 rows=json.loads(output.read_text());profile={r['name']:r for r in rows};assert len(rows)==len(profile)
 return profile,output
save()
try:
 assert sha(V)=='626e3f21ba70fb417ad1085995a88b4af217a1b6f210191fa58ca442aad0098a'
 T=R/'research/rmaf/monitoring/global-next-20261016T085803Z/GLOBAL-SOURCE-TARGET-v2.json';assert sha(T)=='1b20034e34b9e6902572af6273abdcccf121dd09f6257362e88b2c8c9a160db9';t=json.loads(T.read_text())
 for p in [Path(__file__),D/'audit_v1.py',P/'certificate.json',V,Path(A.__file__),Path(G.__file__),T,B/'SEED.json',B/'common-scalar-extension-v1.json',D/'compile_v1.py',D/'CONTROLS-PIN-v1.md']:
  rec['inputs'][str(p.relative_to(R))]=sha(p)
 for k in ['call_count','early','rule5_classifier','rule5common','checker']:
  e=t['allowed_packages'][k];assert sha(R/e['manifest'])==e['sha256']
 oldM=json.loads((R/t['allowed_packages']['call_count']['manifest']).read_text());oldC=R/oldM['canonical_certificate'];assert sha(oldC)==oldM['certificate_sha256'];old=json.loads(oldC.read_text())
 rec['controls']['completed_engine_controls_inherited']=dict(certificate=str(oldC.relative_to(R)),sha256=sha(oldC),controls=old['controls'],independent=False)
 records={e['module']:e for e in old['reused_producers']+old['new_producers']}
 oldSources={e['module']:e for e in old['sources']}
 receipts=[]
 for p in B.glob('compile-*/receipt.json'):
  c=json.loads(p.read_text())
  if c.get('status')=='PASS_AUTHOR_GUARDED_SOURCE_COMPILE':receipts.append((p,c))
 for n in sorted(full|{'FullSourceControls'}):
  assert sha(D/(n+'.lean'))==sha(B/(n+'.lean'))
  assert any(r['module']==n and r['exit']==0 and r['source_sha256']==sha(D/(n+'.lean')) for p,c in receipts for r in c['runs']),('NO_COMPILE_RECEIPT',n)
 neg=[(p,c) for p,c in receipts if any(r['module']=='FullSourceFalseControls' and r['exit']==1 and r['source_sha256']==sha(D/'FullSourceFalseControls.lean') for r in c['runs'])];assert neg
 p,c=neg[-1];log=(p.parent/'FullSourceFalseControls.log').read_text();errs=re.findall(r': error(?:\([^)]*\))?: ([^\n]*)',log)
 assert len(errs)==2 and 'sorry' not in log and all(e=='unsolved goals' or e.startswith('Tactic `decide` proved that the proposition') for e in errs)
 rec['controls']['two_targeted_corruptions']=dict(receipt=str(p.relative_to(R)),sha256=sha(p),errors=errs)
 def closure(root,starts):
  order=[];seen=set()
  def visit(n):
   if n in seen:return
   p=root/(n+'.lean');assert p.exists(),n
   for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
    if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
   seen.add(n);order.append(n)
  for n in starts:visit(n)
  return order
 order=closure(B,['FullSourceControls','ClassifierPayload'])
 for n in order:
  p=B/(n+'.lean');o=B/(n+'.olean')
  rec['sources'].append(dict(module=n,source_sha256=sha(p),olean_sha256=sha(o)))
 (O/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
 assert (P/'Header.lean').read_text()==header_source(order)
 hlog=(P/'Header.log').read_text();counts,expected=parse_header(hlog,order,B)
 def check(n,rows,cnts=counts,exp=expected):
  A.parse_producer(dict(producer=n,count=cnts[n]),rows)
  assert [(r['index'],r['actual_name'],r['kind']) for r in rows]==exp[n],('HEADER_MISMATCH',n)
  for r in rows:
   if r['kind'] in {'definition','opaque'}:assert r['has_body'] and r['body']!='<none>'
 baseRows={};merged=[];fresh=[]
 for n in order:
  if n in records and n in oldSources and sha(B/(n+'.lean'))==oldSources[n]['source_sha256'] and sha(B/(n+'.olean'))==oldSources[n]['olean_sha256']:
   e=records[n];p=R/e['path'];assert sha(p)==e['sha256'];rows=read_rows(p);check(n,rows)
   baseRows[n]=fingerprint(rows);merged+=baseRows[n];rec['reused_producers'].append(e)
  else:fresh.append(n)
 print('CLOSURE',len(order),'FRESH',len(fresh),flush=True);save()
 # Compare every source-identical/object-distinct common dependency in its
 # original imported context against the exact chosen completed pool.
 mm=json.loads((R/t['allowed_packages']['rule5common']['manifest']).read_text());M=R/mm['canonical_receipt']['receipt'];pins={e['path']:e['sha256'] for e in mm['immutable_files']}
 altOrder=closure(M,['CommonLocalBinding','ScalarEnvelope']);different=[]
 for n in altOrder:
  p=M/(n+'.lean');o=M/(n+'.olean')
  assert sha(p)==pins[str(p.relative_to(R))] and sha(o)==pins[str(o.relative_to(R))]
  if n in baseRows:
   assert sha(p)==sha(B/p.name),('NONPROOF_SOURCE_VERSION_DIFFERENCE',n)
   if sha(o)!=sha(B/o.name):different.append(n)
 if different:
  assert (P/'AlternativeHeader.lean').read_text()==header_source(altOrder)
  ah=(P/'AlternativeHeader.log').read_text();ac,ae=parse_header(ah,altOrder,M)
  planted={'Test':dict(name='Test',kind='inductive',full_constant_info='numParams=1')}
  metadata_compare(planted,planted)
  try:metadata_compare(planted,{'Test':dict(name='Test',kind='inductive',full_constant_info='numParams=2')})
  except AssertionError:rec['controls']['full_metadata_corruption']='CAUGHT'
  else:raise AssertionError('METADATA_CORRUPTION_ACCEPTED')
  for i,n in enumerate(different):
   saved=P/('records-Version'+str(i))/(n+'.json.gz')
   if saved.exists():p=saved
   else:
    idx,folder=extract(O,altOrder,[n],M,'Version'+str(i));assert not idx['rejects'];e=idx['producer_counts'][0];p=folder/e['file']
   rows=read_rows(p);check(n,rows,ac,ae)
   comparison=G.inspect(baseRows[n]+fingerprint(rows))
   assert all(r['decision']=='NONPROOF_METADATA_UNCHECKED' for r in comparison['rejects']),('NONPROOF_VERSION_DIFFERENCE',n,comparison['rejects'])
   bridge=None
   if comparison['rejects']:
    chosen,cp=metadata_profile(B,n,'Chosen'+str(i));alternative,ap=metadata_profile(M,n,'Alternative'+str(i))
    names={r['name'] for r in comparison['rejects']}
    assert set(chosen)==names and set(alternative)==names
    metadata_compare(chosen,alternative)
    bridge=dict(decision='EXACT_FULL_CONSTANTINFO_METADATA_EQUAL',chosen=str(cp.relative_to(R)),chosen_sha256=sha(cp),alternative=str(ap.relative_to(R)),alternative_sha256=sha(ap),declarations=len(names))
   oldNames={r['actual_name'] for r in baseRows[n]};newNames={r['actual_name'] for r in rows};assert oldNames==newNames
   rec['version_compatibility'].append(dict(module=n,source_sha256=sha(M/(n+'.lean')),chosen_olean_sha256=sha(B/(n+'.olean')),alternative_olean_sha256=sha(M/(n+'.olean')),record=str(p.relative_to(R)),record_sha256=sha(p),decision='EXACT_TYPE_AND_NONPROOF_BODY_COMPATIBLE',metadata_bridge=bridge,theorem_proofs='Allowed proof variation; full source and axiom closure retained'))
   save()
 print('OBJECT_VERSION_COMPATIBLE',len(different),flush=True)
 total=0
 for i,n in enumerate(fresh):
  idx,folder=extract(O,order,[n],B,'Source'+str(i));assert not idx['rejects'];e=idx['producer_counts'][0];p=folder/e['file'];rows=read_rows(p);check(n,rows)
  total+=p.stat().st_size;assert total<=256*(1<<20)
  if n in full:assert all(r['body_text_scope']=='FULL_ALL_BODY' for r in rows)
  merged+=fingerprint(rows);rec['new_producers'].append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),stored_occurrences=len(rows),compressed_bytes=p.stat().st_size,full_proof_bodies=n in full))
  save();print('SOURCE_EXTRACTED',i+1,'OF',len(fresh),flush=True)
 assert len(merged)==sum(counts.values());compat=G.inspect(merged);assert not compat['rejects'];(O/'COMPATIBILITY.json').write_text(json.dumps(compat,indent=2)+'\n')
 axioms=sorted({a for r in merged for a in r['axiom_references']});assert set(axioms)<=A.ALLOWED
 for e in rec['sources']:
  assert sha(B/(e['module']+'.lean'))==e['source_sha256'] and sha(B/(e['module']+'.olean'))==e['olean_sha256']
 for p,h in rec['inputs'].items():assert sha(R/p)==h
 rec.update(status='PASS_AUTHOR_PREFIX_WEIGHTED_COMMON_AGREEMENT_SOURCE_STAGE',actual_imported_modules=len(order),fresh_producer_modules=len(fresh),full_proof_body_modules=len(full),stored_declarations=len(merged),axiom_union=axioms,compressed_bytes=total,
 scope='Actual Nat prefix subtotal through the total ordered ordinary tree; correct c^q-weighted reservoir induction; full local common construction/guard/callback/expansion bill; general RMAF.agreement value/K bridge and actual common candidate consumer at cells<=12n+1, labels<2^(L+2). Remaining child/Rule4/hard2/selected Rule5 local assembly, full recursive source/bit/native cost remains OPEN.')
 save();print(rec['status'],len(order),len(fresh),len(merged),flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
