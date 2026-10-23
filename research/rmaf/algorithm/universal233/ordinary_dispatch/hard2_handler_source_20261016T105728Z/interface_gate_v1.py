from pathlib import Path
import gzip,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/json.loads((D/'BUILD-v1.json').read_text())['directory'];C=B/'author-audit-v2/certificate.json';c=json.loads(C.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert c['status']=='PASS_AUTHOR_GOOD_PAIR_FULL_SOURCE_BOUND_AND_ORDINARY_PREPARATION_STAGE'
rows={}
for e in c['new_producers']:
 p=R/e['path'];assert sha(p)==e['sha256']
 for r in json.load(gzip.open(p,'rt')):rows[r['actual_name']]=r
prefix='OrdinaryDispatch.Hard2SourceWork.'
required={'goodPairLocalSource':['AllGoodDP.LocalWork.meterRun',prefix+'ownedMeter',prefix+'localTargetMeter',prefix+'appendLabelsMeter',prefix+'additionalCostMeter',prefix+'checkedMeter'],
 'goodPairSource_split':[prefix+'callsForestDebit_split',prefix+'goodPairLocalSource_value'],
 'goodPairSource_bound':[prefix+'goodPairLocalSource_bound',prefix+'callsForestDebit_weighted','OrdinaryDispatch.GoodPairDP.runPair_mass'],
 'selected_goodPairSource_bound':[prefix+'goodPairSource_bound','Universal233.Hard2Overlap.select_sound','Universal233.Hard2Overlap.actual_source_inputs'],
 'hardPaidSource_uniform_bound':[prefix+'hardPaidSource_bound',prefix+'hardPaid_caseMass_uniform'],
 'ordinarySlotMeter':['OrdinaryDispatch.EarlyLocalWork.meterPretest','OrdinaryDispatch.EarlyLocalWork.meterForest','GenericForest.CheckCorrespondence.meterRestrict'],
 'ordinaryPrepareMeter_value':[prefix+'ordinarySlotMeter_value'],
 'ordinaryPrepareMeter_bound':[prefix+'ordinarySlotMeter_bound']}
for short,refs in required.items():
 r=rows[prefix+short];assert all(ref in r['direct_references'] for ref in refs),(short,refs,r['direct_references'])
runtime=['appendLabelsMeter','localTargetMeter','ownedMeter','additionalCostMeter','callsForestDebit','goodPairLocalSource','goodPairSource','properBlockMeter','ordinarySlotMeter','ordinaryPrepareMeter']
for short in runtime:
 r=rows[prefix+short];assert r['kind']=='definition' and r['has_body'] and r['body']!='<none>'
 for ref in r['direct_references']:
  assert not any(x in ref for x in ['Classical.choose','minimumCallback','ExactSolverHyp','OrdinaryIH','Universal233.PaidQueries.meterSchedule','Universal233.PaidQueries.meterRun']),('RUNTIME_UNPROVED_PROFILE_OR_PROOF',short,ref)
controls=['owned_duplicate_occurrences','local_restriction_literal','repeated_union_has_copy_fee','q1_refusal_paid','q2_positive_dp_blocks_callback','q3_actual_residual_and_reconstruction','q3_forest_local_debit_paid','proper_block_original_scans','resolved_slot_literal','prepare_refuses_but_charges_tail']
for n in controls:assert rows[prefix+'HandlerControls.'+n]['kind']=='theorem'
assert c['version_compatibility']==[] and c['axiom_union']==['Classical.choice','Quot.sound','propext']
result=dict(status='PASS_AUTHOR_EXACT_GOODPAIR_PREPARE_INTERFACE_DEPENDENCY_GATE',audit=str(C.relative_to(R)),audit_sha256=sha(C),runtime=runtime,required_direct_references=required,known_answer_theorems=controls,independent_credit=0,all_global_native_milestones='OPEN')
(B/'INTERFACE-DEPENDENCY-GATE-v1.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'])
