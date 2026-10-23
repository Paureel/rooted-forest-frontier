#!/usr/bin/env python3
"""Seal exact scoped original-pair depth01 review and preserve every attempt."""
from pathlib import Path
import json,hashlib,shutil,datetime
H=Path(__file__).resolve().parent;ROOT=next(p for p in H.parents if (p/'bootloops-python').is_file());R=ROOT/'research/rmaf/results'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def load(tag,v=1):return json.loads((R/f'algorithm-depth-one-fresh-{tag}-v{v}.json').read_text())
prior=[]
for path,want,count in [('research/rmaf/algorithm/verification/depth-one-2026-10-15/frozen-ready-v1','bcff1ad2931ec9991cb5de7c09bf8afa44253484602e38aec95e6d508e3fb787',46),('research/rmaf/algorithm/verification/rank-restriction-2026-10-15/frozen-review-v1','615411115f301b02da3fa082036048c6c95487d0ebc26d79faacbfa4adf9c685',372),('research/rmaf/algorithm/verification/rank-restriction-2026-10-15/frozen-ready-v1','b27e9a0401a36be36c05ba119acbad0055c9d56593aab868a70662f82472ab0e',32),('research/rmaf/algorithm/verification/pair-case-2026-10-15/frozen-review-v2','59aaecf285bdbf2b1a98c869e21c32e35c191bd0140f055f32f7e497914cb8a2',196)]:
 d=ROOT/path;mp=d/'MANIFEST.json';assert sha(mp)==want;m=json.loads(mp.read_text());assert len(m['files'])==count
 for f,w in m['files'].items():assert sha(d/f)==w
 prior.append({'manifest':str(mp.relative_to(ROOT)),'sha256':want,'entries_rechecked':count})
pins=json.loads((H/'RELEASED-PINS-v2.json').read_text());assert sha(ROOT/pins['manifest'])==pins['manifest_sha256']=='d776b06ea6039850ba0e333908e18d2d95cd7ae4138e224d5859fb324e300032';assert len(pins['matched_files'])==317
for row in pins['matched_files']:assert sha(ROOT/row['path'])==row['sha256'] and (ROOT/row['path']).stat().st_size==row['bytes']
assert sha(ROOT/pins['canonical_receipt'])==pins['canonical_receipt_sha256']
source=load('source-rebuild');detail=load('details');actual=load('actual-definitions');iface=load('interface-gates',3);blind=load('released-battery');std=load('std-gates')
assert source['verdict']=='PASS-ISOLATED-SOURCE-ONLY-DEPTH01-REBUILD-AND-COMPLETE-ORIGIN-AUDIT'
assert len(source['order'])==39 and source['audits']['FreshOriginAudit']['total']==2041 and source['origin_counts_equal_canonical']
assert all(row['current_origin_hash_match'] for row in source['bindings'])
for row in source['bindings']:assert sha(H/'isolated-release-v1'/(row['module']+'.lean'))==row['frozen_source_sha256']
assert detail['verdict'].startswith('PASS-') and len(detail['declarations'])==2041 and detail['private_declarations']==211
assert len(detail['executable_scientific_closure'])==117
assert actual['verdict'].startswith('PASS-') and len(actual['comparisons'])==196 and all(row['passed'] for row in actual['comparisons'])
assert len(actual['result_witnesses'])==13 and all(row['accepted'] for row in actual['result_witnesses'])
assert iface['verdict']=='PASS-EXACT-INTERFACES-FIVE-FALSE-CLAIMS-AND-ORIGINAL-PAIR-SLOT-SEAM'
assert iface['audits']['FreshFinalOriginAudit']['total']==2042 and not any(row['rejected'] for row in iface['audits']['FreshFinalOriginAudit']['rows'])
assert sum(row['false_propositions_rejected'] for row in iface['false_controls'].values())==5 and iface['false_controls']['FalseSourceColor']['false_propositions_rejected']==0
assert blind['literal_checks']==blind['mismatches_rejected']==196 and blind['verdict'].startswith('PASS-')
assert std['verdict']=='PASS-BLIND-STD-TOY-FALSE-CUSTOM-PRIVATE-IMPORT-AND-INVENTORY-GATES'
runtime=json.loads((H/'RUNTIME-REVIEW-v1.json').read_text())
for row in runtime['pinned_Std_sources_rechecked']:assert sha(Path(row['path']))==row['sha256']
counts={'cost0':0,'cost1':0,'rejected':0,'refused':0}
for row in actual['result_witnesses']:
 v=row['actual'];k='refused' if v['status']=='REFUSED' else 'rejected' if v['status']=='MINIMUM_AT_LEAST_2' else 'cost'+str(v['cost']);counts[k]+=1
assert counts=={'cost0':4,'cost1':4,'rejected':2,'refused':3}
summary={'status':'SCOPED_NONAUTHOR_CONFIRMED','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Actual ordinary original-pair exact0/1 MAF pretest with literal original cut/global minimum; rejection lower bound; guard iff','root_target_sha256':sha(H/'TARGET-v1.md'),'author_manifest_sha256':pins['manifest_sha256'],
 'claims':{'proper_guard_iff':'NONAUTHOR-CONFIRMED','universal_cost0_1_completeness':'NONAUTHOR-CONFIRMED','success_global_original_minimum':'NONAUTHOR-CONFIRMED','literal_original_zero_one_RealizedOutput':'NONAUTHOR-CONFIRMED','rejected_original_minimum_at_least_two':'NONAUTHOR-CONFIRMED','own_original_pair_resolved_slots':'LEAN-PROVED and full-origin audited','source_runtime':'O(N^4(b+1))/O(M^5) CONFIRMED UNDER EXPLICIT PRIMITIVE-OPERATION CONTRACT','compiled_fine_instruction_cost_refinement':'OPEN_NOT_SUPPLIED','whole_state_scheduler_instantiation':'OPEN_BARRED_IMPLEMENTATION_UNREVIEWED','recursive_witness_reconstruction':'OPEN','termination_and_global_faster_runtime':'OPEN','Algorithm':'OPEN','Correctness':'OPEN','Smaller_base':'OPEN','novelty':'NOT_CLAIMED'},
 'lineage':{'same_reviewer_as_prior_G_E_rank':True,'own_frozen_graph_checker_reused':True,'source_edge_and_partition_routes_share_graph_topology_layer':True,'Lean_origin_API_shared_validation_layer':True,'extra_independent_replications':0,'author_contacts':0,'children':0,'author_runners_or_auditors_executed':0},
 'preparation':{'immutable_readiness_files':46,'blind_literal_controls':196,'mismatched_expectation_mutations_rejected':196,'Std_toy_clean_origins_declarations':19,'dirty_client_declarations':7,'dirty_rejections':6,'custom_axioms':3,'candidate_contact_before_READY':False},
 'actual_definition_checks':{'literal_comparisons':196,'returned_result_checks':13,'original_edge_forests':48,'one_two_block_partitions':61,'all_partitions':106,'restriction_root_hull_rows':6,'maximum_fixture_labels':4,'maximum_fixture_partition_denominator':15,'outcomes':counts,'ties':'All frozen valid minimum witnesses retained; no candidate tie-order assumption','candidate_false_claims_rejected':5,'author_ambiguous_postproof_draft_false_credit':0},
 'source_bound_audit':{'author_files_rechecked':317,'source_modules':39,'source_origin_declarations':2041,'private_declarations':211,'final_modules_with_own_slots':40,'final_origin_declarations':2042,'canonical_origin_counts_equal':True,'original_counts_unchanged_after_own_module':True,'permitted_axioms_only':['propext','Classical.choice','Quot.sound'],'scientific_oleans_copied':0,'candidate_source_edits':0,'filename_import_body_adapters':0,'executable_dependency_closure_names':117,'hidden_exponential_runtime_oracles_absent':detail['forbidden_runtime_oracles_absent'],'whole_source_type_records_and_body_hashes_retained':True},
 'author_control_timing':{'v1':'Declared preproof author development bank, not independent certification','supplement_v2':'Postproof direct source-color controls; ambiguity failure retained without false credit','supplement_v3':'Fully qualified intended false proposition rejected','reviewer_blind_bank':'Frozen and executed before any depth_one source/control/receipt/auditor contact'},
 'retained_reviewer_failures':[{'artifact':'RELEASED-PINS-v1.json','cause':'Loop-shadowed manifest path metadata; all317 byte checks and correct manifest SHA unaffected','resolution':'RELEASED-PINS-v2.json corrects path, v1 retained'},{'receipt':'interface-gates-v1','cause':'Diagnostic case expected ambiguous but Lean prints Ambiguous','resolution':'v2 exact diagnostic case; no mathematical false credit changed'},{'receipt':'interface-gates-v2','cause':'Own slot proof supplied old equation after dependent cases rewrote the goal; failed error-recovery sorryAx received no credit','resolution':'PretestSlotsV2 replaces three equality terms with rfl; same statement, final40-origin standard-only audit passes'}],
 'unsupported_or_timeouts':0,'prior_immutable_seals_rechecked':prior,'acceptance_basis':'Fresh semantic rederivation, original source/runtime audit, source-only kernel replay and all-origin/type/body-hash/axiom/path audit; finite fixtures interpret definitions, not universal proof','remaining_conditions':['Whole-state/local-pair guard instantiation and storage of resolved slots','Recursive original witness reconstruction','Total scheduler states and termination','Compiled fine-instruction cost refinement if required','Complete faster algorithm/global base and novelty']}
sp=R/'algorithm-depth-one-fresh-review-v1.json';sp.write_text(json.dumps(summary,indent=2)+'\n')
timing={'source_compile_seconds':sum(r['seconds'] for r in source['runs'] if r['module']!='FreshOriginAudit'),'source_full_origin_audit_seconds':sum(r['seconds'] for r in source['runs'] if r['module']=='FreshOriginAudit'),'actual_definition_readout_seconds':sum(r['seconds'] for r in actual['runs']),'full_signature_path_closure_seconds':sum(r['seconds'] for r in detail['runs']),'final_slot_compile_and_audit_seconds':sum(r['seconds'] for r in iface['runs']),'scope':'Measured bounded verification only; no asymptotic conclusion from timing/CPU/exit status'}
(H/'TIMING-RELEASE-v1.json').write_text(json.dumps(timing,indent=2)+'\n')
D=H/'frozen-review-v1';assert not D.exists();D.mkdir()
for p in H.iterdir():
 if p.is_file():shutil.copy2(p,D/p.name)
for p in (H/'isolated-release-v1').rglob('*'):
 if p.is_file() and p.suffix not in ['.olean','.ilean','.pyc']:
  q=D/p.relative_to(H);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
(D/'results').mkdir()
for p in sorted(R.glob('algorithm-depth-one-fresh-*-v*.json')):shutil.copy2(p,D/'results'/p.name)
files={str(p.relative_to(D)):sha(p) for p in sorted(D.rglob('*')) if p.is_file()};m={'status':'SCOPED_NONAUTHOR_CONFIRMED','file_count':len(files),'files':files,'external_prior_seals':prior,'author_manifest_sha256':pins['manifest_sha256'],'all_three_main_milestones':'OPEN','extra_replications':0}
mp=D/'MANIFEST.json';mp.write_text(json.dumps(m,indent=2)+'\n')
for path,w in files.items():assert sha(D/path)==w
seal={'manifest':str(mp.relative_to(ROOT)),'sha256':sha(mp),'entries':len(files),'summary':str(sp.relative_to(ROOT)),'summary_sha256':sha(sp),'status':'SCOPED_NONAUTHOR_CONFIRMED','all_three_main_milestones':'OPEN'}
(H/'REVIEW-SEAL-v1.json').write_text(json.dumps(seal,indent=2)+'\n')
for p in D.rglob('*'):p.chmod(p.stat().st_mode & ~0o222)
D.chmod(D.stat().st_mode & ~0o222);print(json.dumps(seal))
try:
 from telemetry import artifact,metric,gate
 artifact(str(sp));artifact(str(mp));metric('actual definition comparisons',196,total=196,unit='comparisons');metric('actual pretest outcomes',13,total=13,unit='fixtures');gate('known_truth','passed',detail='Scoped original-pair depth01 theorem/source-cost audit; whole state and all3main milestones OPEN')
except ImportError:pass
