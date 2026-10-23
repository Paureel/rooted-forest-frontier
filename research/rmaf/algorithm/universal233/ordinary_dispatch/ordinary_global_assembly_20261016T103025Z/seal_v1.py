# Freeze only new own files; preserve every original source/object mode/inode.
from pathlib import Path
import datetime,hashlib,json,re,stat
D=Path(__file__).resolve().parent;R=D.parents[5];B=D/'build';C=B/'author-audit-v5/certificate.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def fileinfo(p):
 s=p.stat();return {'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':s.st_size,'mode':oct(stat.S_IMODE(s.st_mode)),'inode':s.st_ino}
assert not (D/'FINAL-MANIFEST-v1.json').exists()
c=json.loads(C.read_text());assert c['status']=='PASS_AUTHOR_PARTIAL_ORDINARY_SOURCE_AND_ACTUAL_OPTIMIZER_COMPOSITION'
logical={'ClosedLocalSource','ClosedSourceTree','OptimizerSourceBodies','OptimizerSourceUniform'};control={'GlobalAssemblyControls','OptimizerAssemblyControls'};allowed={'Classical.choice','Quot.sound','propext'}
assert {x['module'] for x in c['new_producers'] if x['all_proof_bodies']}==logical
for x in c['new_producers']:
 assert sha(R/x['path'])==x['sha256'];assert sha(B/(x['module']+'.lean'))==x['source_sha256'];assert sha(B/(x['module']+'.olean'))==x['olean_sha256'];assert x['raw_bytes']<64*(1<<20);assert set(x['axiom_union'])<=allowed
 if x['module'] in logical|control:assert sha(D/(x['module']+'.lean'))==x['source_sha256']
for x in c['reused_producers']:assert sha(R/x['path'])==x['sha256']
assert set(c['axiom_union'])==allowed
for k in ['hard2_front','rule4_bound']:
 p=R/json.loads((D/'PINNED-PACKAGES-v1.json').read_text())[k]['manifest'];m=json.loads(p.read_text());z=json.loads((R/m['canonical_certificate']).read_text());assert set(z['axiom_union'])<=allowed
receipts=[]
for p in B.glob('compile-*/receipt.json'):
 z=json.loads(p.read_text())
 if z.get('status')=='PASS_AUTHOR_GUARDED_SOURCE_COMPILE':receipts.append((p,z))
checks={'positive':[],'mathematical_rejections':[],'hash_control':json.loads((D/'HASH-CONTROL-v1.json').read_text()),'producer_controls':c['controls'],'compatibility_controls':json.loads((B/'compatibility-v2/certificate.json').read_text())['controls']}
for n in sorted(logical|control|{'PublicTypes'}):
 matches=[(p,z,x) for p,z in receipts for x in z['runs'] if x['module']==n and x['exit']==0 and x['source_sha256']==sha(D/(n+'.lean'))];assert matches,n
 p,z,x=matches[-1];checks['positive'].append({'module':n,'receipt':str(p.relative_to(R)),'receipt_sha256':sha(p),'source_sha256':x['source_sha256'],'log_sha256':x['log_sha256']})
for n,count in [('GlobalAssemblyFalseControls',2),('OptimizerAssemblyFalseControls',3)]:
 matches=[(p,z,x) for p,z in receipts for x in z['runs'] if x['module']==n and x['exit']==1 and x['source_sha256']==sha(D/(n+'.lean'))];assert matches,n
 p,z,x=matches[-1];log=(p.parent/(n+'.log')).read_text();errs=re.findall(r': error(?:\([^)]*\))?: ([^\n]*)',log);assert len(errs)==count and all(e.startswith('Tactic `decide` proved that the proposition') for e in errs) and 'sorry' not in log
 checks['mathematical_rejections'].append({'module':n,'receipt':str(p.relative_to(R)),'receipt_sha256':sha(p),'source_sha256':x['source_sha256'],'log_sha256':x['log_sha256'],'mathematical_errors':len(errs)})
(D/'CONTROLS-EXECUTED-v1.json').write_text(json.dumps(checks,indent=2)+'\n')
pins=json.loads((D/'PINNED-PACKAGES-v1.json').read_text());checked=set()
for k,e in pins.items():
 p=R/e['manifest'];s=p.stat();assert sha(p)==e['sha256'] and s.st_ino==e['inode'] and oct(stat.S_IMODE(s.st_mode))==e['mode'],k
ctx=json.loads((D/'DEPENDENCY-PROVENANCE-v4.json').read_text());originals=[]
for e in ctx['modules']:originals.extend([e['source'],e['object']])
for e in ctx['optimizer_context']['object_differences']:originals.extend([e['alternative']['source'],e['alternative']['object']])
for e in originals:
 if e['path'] in checked:continue
 p=R/e['path'];s=p.stat();assert sha(p)==e['sha256'] and s.st_ino==e['inode'] and oct(stat.S_IMODE(s.st_mode))==e['mode'],e['path'];checked.add(e['path'])
hardlinks=0;copies=0
for e in ctx['modules']:
 for k in ['source','object']:
  x=e[k];p=R/x['path'];q=B/p.name;assert sha(q)==x['sha256'] and not q.stat().st_mode&0o222
  if q.stat().st_ino==p.stat().st_ino:hardlinks+=1
  else:assert p.stat().st_mode&0o222;copies+=1
T=R/'research/rmaf/monitoring/next-20261016T103025Z/GLOBAL-COST-ASSEMBLY-TARGET-v1.json';assert sha(T)=='987a6ece367a6bfc8fc945bd33df053f120e10a35399e039b8214eacd306b387'
pinreport={'version':1,'manifest_pins_preserved':len(pins),'selected_source_object_pairs':len(ctx['modules']),'distinct_original_files_rechecked':len(checked),'source_object_hashes_modes_inodes_preserved':True,'readonly_hardlinks':hardlinks,'readonly_own_copies_of_pinned_writable_originals':copies,'target_sha256':sha(T)}
(D/'PIN-RECHECK-v1.json').write_text(json.dumps(pinreport,indent=2)+'\n')
with (D/'WORKFILE-v1.md').open('a') as f:f.write('\nThe author audit-v5 passed. Four retained failed audits precede it: two stdout-cap stops, the overstrict producer/resolved-origin assertion, and the unavailable Repr ConstantInfo extractor attempt. The successful adapter retains every occurrence and checks exact types for re-emitted theorem names; nonproof collisions are rejected. All four new logical modules have full proof text below64MiB each, and printed logical roots use only propext/Classical.choice/Quot.sound. Positive/negative controls, original-context compatibility, public types and pin rechecks are retained. This is a frozen partial assembly boundary, pending the literal handler sheets named in FIRST-GAP-v1.json.\n')
owned=[]
for p in sorted(D.rglob('*')):
 if not p.is_file() or p.name=='FINAL-MANIFEST-v1.json':continue
 assert not p.is_symlink()
 if p.stat().st_nlink>1:assert not p.stat().st_mode&0o222;continue
 p.chmod(0o444);owned.append(fileinfo(p))
m={
 'version':1,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'status':'FROZEN_AUTHOR_PARTIAL_ORDINARY_SOURCE_AND_ACTUAL_OPTIMIZER_COMPOSITION_REVIEW_PENDING',
 'no_further_writes':True,'no_write_boundary':str(D.relative_to(R)),'own_directory':str(D.relative_to(R)),
 'target':str(T.relative_to(R)),'target_sha256':sha(T),'canonical_build':str(B.relative_to(R)),
 'canonical_import':'OptimizerSourceUniform','canonical_certificate':str(C.relative_to(R)),'certificate_sha256':sha(C),
 'result':str((D/'RESULT-v1.md').relative_to(R)),'source_interface':str((D/'INTERFACE-v1.json').relative_to(R)),
 'printed_interface':str((D/'PUBLIC-TYPES-v1.txt').relative_to(R)),'first_gap':str((D/'FIRST-GAP-v1.json').relative_to(R)),
 'dependency_provenance':str((D/'DEPENDENCY-PROVENANCE-v4.json').relative_to(R)),'dependency_provenance_sha256':sha(D/'DEPENDENCY-PROVENANCE-v4.json'),
 'import_compatibility':c['compatibility_bridge'],'pin_recheck':pinreport,
 'main_interface':'OrdinaryDispatch.GlobalSourceAssembly.partialSourceOptimize_bound',
 'query_interface':'OrdinaryDispatch.GlobalSourceAssembly.closedSourceSubtotal_bound',
 'optimizer_conditional_interface':'OrdinaryDispatch.GlobalSourceAssembly.sourceOptimize_uniform_233',
 'actual_fees_interface':'OrdinaryDispatch.GlobalSourceAssembly.sourceOptimize_actual_fees',
 'counter_scope':'Explicit closed PARTIAL local/source subtotal: prefix+common+one/high+Rule4+hard2-front; full ordinary query tree. Literal actual optimizer wrapper and new source-metered final recovery. Remaining hard2/Rule5 handler local bills are absent.',
 'value_agreement':'partialSourceMeter.value=FastOrdinary.solve; partialSourceOptimize.value=optimize; sourceFinishMeter.value=finish',
 'coefficient':'A(n)=n*(closedLocalPolynomial n n*1024*(n+1))+512*(2*n+1)^2+recoverySourceEnvelope n',
 'base':'233/100','q':'k-1','implicit_rho':False,
 'missing_handler_cost_premises_silently_instantiated':False,
 'generic_query_premise':'sourceOptimize_uniform_233 has an explicit uniform w bound. Its concrete closed-subtotal instance is proved. No full solve-cost instantiation exists.',
 'owned_logical_modules':sorted(logical),'actual_imported_modules':c['actual_imported_modules'],
 'body_qualification':'Full actual types, theorem proof text, nonproof bodies, references and axiom closure for four new logical modules. Own controls and seventeen imported additions have full actual types/nonproof bodies and theorem references/axiom closure with explicit theorem plaintext omission. Existing exact frozen producer qualifications are retained. Re-emitted theorem occurrences are retained with exact loaded-type comparison; nonproof collisions rejected.',
 'axiom_union':c['axiom_union'],'controls_executed':str((D/'CONTROLS-EXECUTED-v1.json').relative_to(R)),
 'retained_failed_audits':[str((B/f'author-audit-v{i}'/'certificate.json').relative_to(R)) for i in range(1,5)],
 'retained_failed_setup':'SETUP-FAILURES-v1.json','retained_failed_compatibility':str((B/'compatibility-v1/certificate.json').relative_to(R)),
 'all_main_milestones':False,'full_ordinary_source_counter':'OPEN','full_ordinary_runtime':'OPEN','abstract_bit_runtime':'OPEN','native_or_ir':'OPEN','independent_acceptance':False,'improved_base_acceptance':'OPEN','novelty':'OPEN',
 'first_unprovided_consuming_statement':json.loads((D/'FIRST-GAP-v1.json').read_text())['first_unprovided_consuming_statement'],
 'immutable_owned_files':owned
}
p=D/'FINAL-MANIFEST-v1.json';p.write_text(json.dumps(m,indent=2)+'\n');p.chmod(0o444)
print('FROZEN',str(p.relative_to(R)),sha(p));print('PARTIAL_ORDINARY_AND_OPTIMIZER_SOURCE_BOUNDARY',len(owned),'owned files; full runtime OPEN')
