# Freeze only new own files; preserve every original source/object mode/inode.
from pathlib import Path
import datetime,hashlib,json,re,stat
D=Path(__file__).resolve().parent;R=D.parents[5];B=D/'build-v2';C=B/'author-audit-v1/certificate.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def fileinfo(p):
 s=p.stat();return {'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':s.st_size,'mode':oct(stat.S_IMODE(s.st_mode)),'inode':s.st_ino}
assert not (D/'FINAL-MANIFEST-v1.json').exists()
c=json.loads(C.read_text());assert c['status']=='PASS_AUTHOR_SELECTED_HARDPAID_EXTENDED_SUBTOTAL_AND_RULE5_EXACT_RESIDUAL_JOIN'
logical={'HardPaidUniform','HardPaidSelection','HardPaidStepJoin','Rule5DispatchJoin','ExtendedTreeOptimizer'};control={'ExtendedControls'};routing={'ExtendedSourceInterface'};allowed={'Classical.choice','Quot.sound','propext'}
assert {x['module'] for x in c['new_producers'] if x['all_proof_bodies']}==logical
for x in c['new_producers']:
 assert sha(R/x['path'])==x['sha256'];assert sha(B/(x['module']+'.lean'))==x['source_sha256'];assert sha(B/(x['module']+'.olean'))==x['olean_sha256'];assert x['raw_bytes']<64*(1<<20);assert (R/x['path']).stat().st_size<16*(1<<20);assert set(x['axiom_union'])<=allowed
 if x['module'] in logical|control:assert sha(D/(x['module']+'.lean'))==x['source_sha256']
for x in c['reused_producers']:assert sha(R/x['path'])==x['sha256']
assert set(c['axiom_union'])==allowed
for k in ['partial_global_assembly','hard_paid']:
 p=R/json.loads((D/'PINNED-PACKAGES-v1.json').read_text())[k]['manifest'];m=json.loads(p.read_text());z=json.loads((R/m['canonical_certificate']).read_text());assert set(z['axiom_union'])<=allowed
receipts=[]
for p in B.glob('compile-*/receipt.json'):
 z=json.loads(p.read_text())
 if z.get('status')=='PASS_AUTHOR_GUARDED_SOURCE_COMPILE':receipts.append((p,z))
checks={'positive':[],'mathematical_rejections':[],'hash_control':json.loads((D/'HASH-CONTROL-v1.json').read_text()),'producer_controls':c['controls'],'compatibility_controls':json.loads((B/'compatibility-v1/certificate.json').read_text())['controls']}
for n in sorted(logical|control|routing|{'PublicTypes'}):
 matches=[(p,z,x) for p,z in receipts for x in z['runs'] if x['module']==n and x['exit']==0 and x['source_sha256']==sha(D/(n+'.lean'))];assert matches,n
 p,z,x=matches[-1];checks['positive'].append({'module':n,'receipt':str(p.relative_to(R)),'receipt_sha256':sha(p),'source_sha256':x['source_sha256'],'log_sha256':x['log_sha256']})
for n,count in [('ExtendedFalseControls',3)]:
 matches=[(p,z,x) for p,z in receipts for x in z['runs'] if x['module']==n and x['exit']==1 and x['source_sha256']==sha(D/(n+'.lean'))];assert matches,n
 p,z,x=matches[-1];log=(p.parent/(n+'.log')).read_text();errs=re.findall(r': error(?:\([^)]*\))?: ([^\n]*)',log);assert len(errs)==count and all(e.startswith('Tactic `decide` proved that the proposition') for e in errs) and 'sorry' not in log
 checks['mathematical_rejections'].append({'module':n,'receipt':str(p.relative_to(R)),'receipt_sha256':sha(p),'source_sha256':x['source_sha256'],'log_sha256':x['log_sha256'],'mathematical_errors':len(errs)})
(D/'CONTROLS-EXECUTED-v1.json').write_text(json.dumps(checks,indent=2)+'\n')
pins=json.loads((D/'PINNED-PACKAGES-v1.json').read_text());checked=set()
for k,e in pins.items():
 p=R/e['manifest'];s=p.stat();assert sha(p)==e['sha256'] and s.st_ino==e['inode'] and oct(stat.S_IMODE(s.st_mode))==e['mode'],k
ctx=json.loads((D/'DEPENDENCY-PROVENANCE-v3.json').read_text());originals=[]
for e in ctx['modules']:originals.extend([e['source'],e['object']])
for e in ctx['object_differences']:originals.extend([e['alternative']['source'],e['alternative']['object']])
for e in originals:
 if e['path'] in checked:continue
 p=R/e['path'];s=p.stat();assert sha(p)==e['sha256'] and s.st_ino==e['inode'] and oct(stat.S_IMODE(s.st_mode))==e['mode'],e['path'];checked.add(e['path'])
hardlinks=0;copies=0
for e in ctx['modules']:
 for k in ['source','object']:
  x=e[k];p=R/x['path'];q=B/p.name;assert sha(q)==x['sha256'] and not q.stat().st_mode&0o222
  if q.stat().st_ino==p.stat().st_ino:hardlinks+=1
  else:assert p.stat().st_mode&0o222;copies+=1
T=R/'research/rmaf/monitoring/producer-assembly-next-20261016T110601Z/GLOBAL-EXTEND-SOURCE-TARGET-v1.json';assert sha(T)=='e92e557beb432fa652e184a2bbee7f89bdc0b41fdab46c829d1ce028f1f67ed8'
pinreport={'version':1,'manifest_pins_preserved':len(pins),'selected_source_object_pairs':len(ctx['modules']),'distinct_original_files_rechecked':len(checked),'source_object_hashes_modes_inodes_preserved':True,'readonly_hardlinks':hardlinks,'readonly_own_copies_of_pinned_writable_originals':copies,'target_sha256':sha(T)}
(D/'PIN-RECHECK-v1.json').write_text(json.dumps(pinreport,indent=2)+'\n')
with (D/'WORKFILE-v1.md').open('a') as f:f.write('\nThe author audit-v1 passed, including full actual proof text for all five new logical modules within the unchanged 64 MiB raw-module, 16 MiB row and 16 MiB compressed caps. Printed roots use only propext/Classical.choice/Quot.sound. The normalized three false controls were rejected mathematically. Original hashes/modes/inodes, setup failure and failed compiler/negative-control evidence are preserved. This is a new frozen PARTIAL ordinary/optimizer bound with an exact UNBOUNDED Rule5 dispatch residual, not a full runtime theorem.\n')
owned=[]
for p in sorted(D.rglob('*')):
 if not p.is_file() or p.name=='FINAL-MANIFEST-v1.json':continue
 assert not p.is_symlink()
 if p.stat().st_nlink>1:assert not p.stat().st_mode&0o222;continue
 p.chmod(0o444);owned.append(fileinfo(p))
m={
 'version':1,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'status':'FROZEN_AUTHOR_SELECTED_HARDPAID_EXTENDED_SUBTOTAL_RULE5_RESIDUAL_JOIN_REVIEW_PENDING',
 'no_further_writes':True,'no_write_boundary':str(D.relative_to(R)),'own_directory':str(D.relative_to(R)),
 'target':str(T.relative_to(R)),'target_sha256':sha(T),'canonical_build':str(B.relative_to(R)),
 'canonical_import':'ExtendedSourceInterface','canonical_certificate':str(C.relative_to(R)),'certificate_sha256':sha(C),
 'result':str((D/'RESULT-v1.md').relative_to(R)),'source_interface':str((D/'INTERFACE-v1.json').relative_to(R)),
 'printed_interface':str((D/'PUBLIC-TYPES-v1.txt').relative_to(R)),'first_gap':str((D/'FIRST-GAP-v1.json').relative_to(R)),
 'dependency_provenance':str((D/'DEPENDENCY-PROVENANCE-v3.json').relative_to(R)),'dependency_provenance_sha256':sha(D/'DEPENDENCY-PROVENANCE-v3.json'),
 'import_compatibility':c['compatibility_bridge'],'pin_recheck':pinreport,
 'main_interface':'OrdinaryDispatch.ExtendedSourceAssembly.extendedPartialOptimize_bound',
 'query_interface':'OrdinaryDispatch.ExtendedSourceAssembly.extendedSourceSubtotal_bound',
 'optimizer_conditional_interface':'OrdinaryDispatch.GlobalSourceAssembly.sourceOptimize_uniform_233',
 'actual_fees_interface':'OrdinaryDispatch.GlobalSourceAssembly.sourceOptimize_actual_fees',
 'counter_scope':'PARTIAL ordinary source subtotal: previously closed local bills plus actual selected runHardPaid generation/execution body. Literal optimizer wrapper and new source recovery once. Rule5 dispatch joins are exact and its local cost is a named UNBOUNDED residual. paidCase inspections/combine/unit local work and other hard2 handlers remain absent.',
 'value_agreement':'extendedPartialOptimize.value=optimize. Actual hardPaid source equals paidCase on the literal used route. Concrete Rule5 dispatch value and rule5Answer projection are exact; value equality does not supply omitted work.',
 'coefficient':'Aprime(n)=n*(extendedLocalPolynomial n n*1024*(n+1))+512*(2*n+1)^2+recoverySourceEnvelope n; extendedLocalPolynomial N Q=old closedLocalPolynomial N Q+hardPaidPolynomial(2*N+3,Q)+16*(2^50*((2*N+3)+Q+2)^8)',
 'base':'233/100','q':'k-1','implicit_rho':False,
 'missing_handler_cost_premises_silently_instantiated':False,
 'generic_query_premise':'The inherited generic optimizer theorem has an explicit uniform w premise. The concrete extended subtotal query bound is proved here and discharges it. No full solve-cost or Rule5 C5 premise is silently instantiated.',
 'owned_logical_modules':sorted(logical),'actual_imported_modules':c['actual_imported_modules'],
 'body_qualification':'Full actual types, theorem proof text, nonproof bodies, references and axiom closure for five new logical modules. Control/aggregation and fifty-four imported additions retain actual types/nonproof bodies/references/AX with explicit theorem plaintext omission. Exact previous-global and hard-paid records preserve all inherited qualifications, including the Hard2SelectedGenerationBound proof-text omission. Cross-origin theorem occurrences are retained with exact loaded-type comparison; nonproof collisions rejected.',
 'axiom_union':c['axiom_union'],'controls_executed':str((D/'CONTROLS-EXECUTED-v1.json').relative_to(R)),
 'retained_failed_audits':[],
 'retained_failed_setup':'SETUP-FAILURES-v1.json','compatibility_certificate':str((B/'compatibility-v1/certificate.json').relative_to(R)),
 'all_main_milestones':False,'full_ordinary_source_counter':'OPEN','full_ordinary_runtime':'OPEN','abstract_bit_runtime':'OPEN','native_or_ir':'OPEN','independent_acceptance':False,'improved_base_acceptance':'OPEN','novelty':'OPEN',
 'first_unprovided_consuming_statement':json.loads((D/'FIRST-GAP-v1.json').read_text())['first_unprovided_consuming_statement'],
 'immutable_owned_files':owned
}
p=D/'FINAL-MANIFEST-v1.json';p.write_text(json.dumps(m,indent=2)+'\n');p.chmod(0o444)
print('FROZEN',str(p.relative_to(R)),sha(p));print('SELECTED_HARDPAID_EXTENDED_SOURCE_BOUNDARY_WITH_UNBOUNDED_RULE5_RESIDUAL',len(owned),'owned files; full runtime OPEN')
