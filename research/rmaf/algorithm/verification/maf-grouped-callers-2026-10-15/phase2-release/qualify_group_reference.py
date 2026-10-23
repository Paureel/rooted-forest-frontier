"""Keep strict failure, qualify only its exact out-of-premise reference defect."""
import json
import rebuild as R
p=R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-groups-readout-v1.json';x=json.loads(p.read_text());assert x['status'].startswith('FAIL_RETAINED')
m=x['reference_mismatches'];assert len(m)==1 and m[0]['id']=='missing-whole-source-ownership' and m[0]['Owns_premise']==False
case=x['actual']['CASE:missing-whole-source-ownership'];assert case['cross'] and not case['ownership'] and case['global_agrees'] and not all(r['agrees'] for r in case['local'])
# The two actually owned sources are leaves1 and3 in separate original target
# cherry regions; source(0,2) belongs to neither group and must not be added to
# CrossClear's quantified sets. This verifies the textual semantic diagnosis.
assert [r['indices'] for r in case['local']]==[[1],[2]]
out={'status':'PASS_APPLICABLE_GROUPED_READOUT_WITH_EXPLICIT_REFERENCE_DEFECT','strict_failed_receipt':str(p.relative_to(R.ROOT)),'strict_failed_receipt_sha256':R.sha(p),'other_actual_comparisons':x['comparisons'],'retained_reference_mismatch':m,'actual_owned_indices':[[1],[2]],'all_universal_reverse_premises_satisfied':False,'no_frozen_expectation_changed':True,'interpretation':'No theorem fire: Owns fails. The frozen reference overstrengthened CrossClear on an unowned source. Actual definition and compiled readout agree. This is not an all-frozen-controls-pass verdict.','all_main_milestones':'OPEN','replication_count_added':0}
q=R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-groups-reference-qualification-v1.json';q.write_text(json.dumps(out,indent=2)+'\n');print(out['status'])
