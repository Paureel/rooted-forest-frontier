#!/usr/bin/env python3
"""Seal this one completed source stage; reuse the frozen source audit evidence."""
from pathlib import Path
import datetime,hashlib,json,os,stat
D=Path(__file__).resolve().parent;R=D.parents[5];O=Path((D/'LAST-FREEZE.txt').read_text().strip());C=json.loads((O/'certificate.json').read_text());S=D/'seal';S.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def wr(p,x):p.write_text(x if isinstance(x,str) else json.dumps(x,indent=2)+'\n')
assert C['status']=='PASS_AUTHOR_COMMON_PAID_EXECUTION_AND_SELECTED_SOURCE_STAGE',C['status']
assert C['axiom_union']==['Classical.choice','Quot.sound','propext']
assert C['controls']['eight_false_execution_claims']=='EIGHT_REJECTED'
assert C['controls']['ExecutionControls']=='RUNTIME_TRUE_CHECKED'
assert len(C['own_modules'])==29
T=R/'research/rmaf/monitoring/rule5-next-20261016T100131Z/RULE5-EXECUTION-TARGET-v1.json';target=json.loads(T.read_text())
assert sha(T)=='d1ed931067c76e99935e907171514588ec444d36ec569336740f3c9cd1efc1e3'
compat=json.loads((D/'DEPENDENCY-COMPATIBILITY-v1.json').read_text())
limits=C['limits'];assert C['resources']['free_bytes']>=3*1024**3 and C['resources']['logical_bytes']<=128*1024**2
cert=dict(path=str((O/'certificate.json').relative_to(R)),sha256=sha(O/'certificate.json'))
api={
 'version':1,'status':'AUTHOR_SOURCE_STAGE_CHECKED_NOT_INDEPENDENT_OR_FULL233_ACCEPTANCE',
 'namespace':'Universal233.Rule5ExecutionSource','target':dict(path=str(T.relative_to(R)),sha256=sha(T)),
 'canonical_build':str(O.relative_to(R)),'certificate':cert,'modules':C['own_modules'],
 'import_paths':[str(O.relative_to(R))]+C['dependency_pool']['paths'],
 'body_audit_qualification':C['body_qualification'],'axiom_union':C['axiom_union'],
 'licenses':target['allowed_packages'],'dependency_compatibility':dict(path=str((D/'DEPENDENCY-COMPATIBILITY-v1.json').relative_to(R)),sha256=sha(D/'DEPENDENCY-COMPATIBILITY-v1.json')),
 'common':{
  'source':'CommonSourceDebit.commonSource (actual declarations are directly in the stage namespace)',
  'value':'common_source_value: exact Rule5CommonOrdinary.runSelectedCommon for every callback/counter',
  'split':'common_source_split: work(W)=work(0)+sum ordered commonJobs W, preserving both calls even after failure',
  'local':'common_source_local: <= commonBudget nt ns (subtreeLabels S d.badArc).length',
  'consumer_domain':'CherryAt T i a b; admitted T S a b=true; actual finalMeter selected remaining d (one e); callback agrees with Rule5LocalWork.actual only on each actual commonJobs member',
  'closed_agreement':'CommonAgreementConsumer.reconstruct_actual_agreement and measuredAgreement_K / agreementK from licensed completed main stage; no stale K fee premise',
  'evidence':['guarded_value','guarded_local','run_paid_value','run_paid_local','common_local_on_jobs','common_call_progress','common_call_size','common_call_bits','common_call_count']},
 'paid':{
  'values':['forest_pretest_value','best_additional_value','current_query_value','current_answer_value','arc_partition_value','current_guard_value','raw_plan_value','requests_value','answers_value','best_for_value','solve_selected_value'],
  'local_polynomial':'solve_selected_prefix_work <= paidExecutionPrefixBudget T S Kc Kl; explicit polynomial definitions compose old builder bounds and new literal execution bounds',
  'domain':'classifier fee Kc only on existing CheckDomain (nt+ns) L; LiteralProps fee Kl only on existing LiteralCallDomain at actual repeated classifier selection; input original labels <2^L',
  'agreement_closed':'Final originalAccepted uses measuredAgreement, with measuredAgreement_K derived from every materialized answer payload via unconditional source soundness, including before originalAccepted runs',
  'forest_counter':'currentQueryMeter executes completed OrdinaryDispatch.WorkRecursion.forestWork cb W only for rejected pretest and residual>1, at exactly the same state/callback/residual',
  'split':'paid_selected_source_split: source work(W)=source work(0)+queryWork W actual ordinaryCalls',
  'query_domain':['request_state_caps','answers_calls_native','solve_selected_calls_native'],
  'literal_boundary':'Distinct LiteralCall -> Nat remains explicit; separate author owns its actual decision/Kl proof; no duplicate predicate proof was authored'},
 'composition':{
  'sources':['runSelectedSource','dispatchSource'],'values':['run_selected_source_value','dispatch_source_value'],
  'splits':['run_selected_source_split','dispatch_source_split'],
  'bill':'run_selected_local_bound: zero-ordinary source work <= selectedPrefixBudget T S Kc Kl z + selectedForestDebit cb classFee literalFee T S a b q z',
  'forest_debit':'selectedForestDebit is the completed implemented forest counter (childForestDebit or paid current-query forestDebit), not an opaque whole-arm fee; common arm uses two direct ordinary calls',
  'local_domain':'CherryAt/admitted/DepthOne.proper; actual final selection; explicit existing classifier and distinct LiteralProps domains; common callback equality only on actual commonJobs',
  'native_trace':['run_selected_calls_native','dispatch_calls_native'],
  'query_domain':['run_selected_query_domain','dispatch_query_domain'],
  'query_conclusion':'Every actual ordinary query budget r<q, DepthOne.proper children, both child leaf counts <= original target leaf count; exact source list retains order and duplicate occurrences'},
 'controls':dict(runtime_true=35,explicit_false_rejected=8,audit_controls=C['controls'],retained_failure_notes=str((D/'failures/fallback-negative-v1.md').relative_to(R))),
 'open':['separately owned LiteralProps actual Kl decision source proof, not supplied here','remaining named classifier primitive CheckDomain/scalar-to-native/binary obligations','global weighted ordinary/forest integration and full2.33 acceptance owned by main','independent acceptance, native operational semantics, recovery and reviews are not asserted']}
wr(S/'PUBLIC-INTERFACE-v1.json',api)
result=f'''# Rule5 execution source stage\n\nThe actual common-one and paid-second execution spines compile, and all five literal runSelected arms plus strict dispatch now have exact value and natural-number callback split theorems. This is an author source stage under the explicit checker/scalar contracts, not full Rule5/2.33, native, or independent acceptance.\n\nThe common spine includes both DepthOne pretests, outsideReply or literal relabel extension, paidJobs construction, the strict two-callback map, runPaid, implemented agreement reconstruction and final length check. A failed first callback still charges the second. The local polynomial uses the supplied completed general agreement K and common agreement consumer. The callback equality contract is restricted to actual commonJobs.\n\nThe paid spine includes the literal raw plan, repeated subtree scans, original-edge arc partition splits, every currentGuard component, guardedPlan filtering, full sourceForest filterMap restriction, requestFor budget/payment, currentAnswer pretest and fallback, strict answer filterMap, original agreement check and List.length best. The source-specific additionalCost pretest score preserves truncated ties; it is not replaced by List.length. The native forest boundary is instantiated with completed forestWork at the exact callback/state/residual. Its ordinary-call debit is split exactly; no whole execution fee replaces these bodies. The separate LiteralProps fee remains explicit on its exact existing domain.\n\nThe combined runSelectedSource and dispatchSource match the frozen source values. Their ordered ordinary query lists equal the existing selected/dispatch traces. Every admitted selected query has a strict smaller budget, proper children and leaf counts bounded by the original target. run_selected_local_bound separates the derived prefix polynomial from implemented GenericForest local work; main owns its weighted integration.\n\nFresh canonical replay: {len(C['own_modules'])} modules, {C['stored_producer_occurrences']} stored producer declarations; all {35} runtime controls true; {8} deliberate false claims explicitly rejected. The fresh auditor caught direct, hidden, unused and dependency axioms; wrong producer order, missing/duplicate rows, foreign paths and changed pins/adapter bytes are controlled. Axiom union: Classical.choice, Quot.sound, propext. All non-theorem and opaque bodies are retained. Theorem proof text alone is omitted, while actual references and axiom closures are traversed. This is the same audit lineage, not an independent check.\n\nCanonical receipt: {O.relative_to(R)}\nCertificate SHA256: {cert['sha256']}\n\nAll licensed prior immutable hashes, modes and inodes were checked before/after replay. Exact dependency source/object pins and the previously licensed 21 object bridges remain explicit in DEPENDENCIES-v1.json and DEPENDENCY-COMPATIBILITY-v1.json. No dependency was rebuilt. Limits: 30 seconds/module, 3072 MiB, 64 MiB raw output, 16 MiB line, 128 MiB logical directory, live 3 GiB free floor.\n\nRetained limitations/failures: every capped development failure and both earlier full replay failures remain. One negative fallback equality did not kernel-reduce through imported forest machinery; the next replacement was refused for a free Setup variable. The final negative suite definitionally reduces paidJobs d 1 length to the closed false proposition 2=1 and explicitly rejects it. The fallback occurrence/debit remains among the 35 runtime controls, with universal value/gate/split proofs separately audited. No native correctness conclusion is inferred. The broad bootloops validation suite was not run: this task uses the scoped Lean replay and source audit only.\n'''
gap='''# Exact remaining frontier\n\nNo common runGuarded/runPaid or paid rawPlan/currentGuard/request/pretest/filter/best execution body is left as a whole-arm fee in this stage. General RMAF.agreement and its K consumer are supplied by completed licensed main inputs and used directly.\n\nThe separate actual LiteralProps decision source meter/Kl polynomial remains with the designated author. The exact retained contract is the prior paid_selected_work LiteralCallDomain premise at an actual repeated finalMeter second selection, with original leaf labels bounded by 2^L. The distinct LiteralCall -> Nat fee has not been discharged or silently merged into classifier Kc.\n\nExisting classifier primitive fees retain their exact CheckDomain (nt+ns) L contract and structural scalar model. Source work is an upper source bill, permitting explicit full-suffix overcharges; it is not a measured native-runtime or binary bit-complexity theorem.\n\nImplemented GenericForest zero-ordinary local work remains in selectedForestDebit. The exact Nat callback split, state domain and strict smaller-budget query contracts are supplied. Main owns the global weighted integration/ordinary induction. For the common arm, a caller must establish equality with the closed callback only on each actual commonJobs member; the stage does not assume arbitrary callbacks return bounded forests.\n\nNo global 2.33 recurrence, numeric/binary/recovery theorem, independent acceptance, native operational semantics or reviewer conclusion is asserted. No unfinished peer/main/reviewer sources, children or peer messages were used.\n'''
wr(D/'FINAL-RESULT-v1.md',result);wr(D/'FIRST-GAP-v1.md',gap)
wr(S/'FINAL-RESULT-v1.md',result);wr(S/'FIRST-GAP-v1.md',gap)
wr(D/'WORKFILE-v1.md',(D/'WORKFILE-v1.md').read_text().replace('Status: execution source proof, control and audit evidence pending.',f"Status: author source stage checked. Canonical replay {O.relative_to(R)}. See FINAL-RESULT-v1.md, FIRST-GAP-v1.md and seal/PUBLIC-INTERFACE-v1.json for exact contracts and remaining scope."))
pilots=[]
for folder in sorted((R/'results').glob('algorithm-universal233-rule5-execution-20261016T100131Z-*')):
 cp=folder/'certificate.json'
 if cp.exists():
  x=json.loads(cp.read_text());pilots.append(dict(path=str(folder.relative_to(R)),certificate_sha256=sha(cp),status=x['status']))
wr(D/'DEVELOPMENT-RECEIPTS-v1.json',pilots)
for p in [D/'FINAL-RESULT-v1.md',D/'FIRST-GAP-v1.md',D/'DEVELOPMENT-RECEIPTS-v1.json',*S.iterdir()]:p.chmod(0o444)
for p in [D/'FINAL-RESULT-v1.md',D/'FIRST-GAP-v1.md',S/'PUBLIC-INTERFACE-v1.json']:
 dest=O/p.name
 assert not dest.exists();dest.write_bytes(p.read_bytes());dest.chmod(0o444)
paths={}
def add(p):
 p=p.resolve();assert p.is_file() and p.is_relative_to(R),p
 k=str(p.relative_to(R));st=p.stat();paths[k]=dict(path=k,sha256=sha(p),mode=st.st_mode,inode=st.st_ino,bytes=st.st_size)
add(T)
for item in target['allowed_packages'].values():
 mp=R/item['manifest'];assert sha(mp)==item['sha256'];add(mp)
 for e in json.loads(mp.read_text()).get('immutable_files',[]):
  p=R/e['path'];assert sha(p)==e['sha256'];add(p)
for e in C['dependencies'].values():
 for key in ['source','olean','loaded_olean']:add(R/e[key])
for folder in [D,O]:
 for p in folder.rglob('*'):
  if p.is_file() and p.name!='FINAL-MANIFEST-v1.json':add(p)
for row in pilots:
 for p in (R/row['path']).rglob('*'):
  if p.is_file():add(p)
# Snapshot the newly created canonical public/result docs too, then recheck all.
for e in paths.values():
 p=R/e['path'];st=p.stat();assert sha(p)==e['sha256'] and st.st_ino==e['inode'] and st.st_mode==e['mode'],e['path']
manifest=dict(version=1,status='PASS_AUTHOR_COMMON_PAID_EXECUTION_AND_SELECTED_SOURCE_STAGE',created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),canonical_build=str(O.relative_to(R)),certificate=cert,target_sha256=sha(T),own_modules=C['own_modules'],stored_producer_occurrences=C['stored_producer_occurrences'],runtime_controls=35,false_claim_rejections=8,axiom_union=C['axiom_union'],body_qualification=C['body_qualification'],independent_acceptance=False,native_semantics=False,full233_acceptance=False,whole_rule5_unconditional_acceptance=False,public_interface=dict(path=str((S/'PUBLIC-INTERFACE-v1.json').relative_to(R)),sha256=sha(S/'PUBLIC-INTERFACE-v1.json')),result=dict(path=str((D/'FINAL-RESULT-v1.md').relative_to(R)),sha256=sha(D/'FINAL-RESULT-v1.md')),gap=dict(path=str((D/'FIRST-GAP-v1.md').relative_to(R)),sha256=sha(D/'FIRST-GAP-v1.md')),dependency_manifest_sha256=sha(D/'DEPENDENCIES-v1.json'),dependency_compatibility_sha256=sha(D/'DEPENDENCY-COMPATIBILITY-v1.json'),prior_immutable_occurrences_matched=C['prior_immutable_occurrences_matched'],limits=C['limits'],immutable_files=sorted(paths.values(),key=lambda x:x['path']))
wr(D/'FINAL-MANIFEST-v1.json',manifest);(D/'FINAL-MANIFEST-v1.json').chmod(0o444)
print(json.dumps(dict(manifest=str((D/'FINAL-MANIFEST-v1.json').relative_to(R)),manifest_sha256=sha(D/'FINAL-MANIFEST-v1.json'),pins=len(paths),modules=len(C['own_modules']),stored_declarations=C['stored_producer_occurrences'],canonical=str(O.relative_to(R))),indent=2))
