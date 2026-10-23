from pathlib import Path
import json,os,subprocess,time,hashlib,importlib.util,sys
H=Path(__file__).resolve().parent;R=next(p for p in H.parents if (p/'bootloops-lean').is_file());F=H/'isolated-source-v1';sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('own_std',H.parent/'frozen-ready-v1/frozen-inputs-v1/std_toy_gates_v1.py');u=importlib.util.module_from_spec(spec);spec.loader.exec_module(u);u.F=F;u.OUT=R/'research/rmaf/results/algorithm-output-state-fresh-actual-detector-gates-v1.json';u.state={'phase':'RELEASED_POSTCONTACT_CONTROLS','candidate_source_mutations':0,'runs':[],'audits':{},'all_main_milestones':'OPEN'}
header='''import FreshActualReadoutsV2
open RMAF RestrictionBridge ForestState ForestGroups OutputState FreshOutputReadouts
'''
claims=[
 ('wrong_target_Q_clear','pairwiseEmbeddings (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] = true','pairwiseEmbeddings (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] = false'),
 ('omitted_source_Q_original','agreement (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] = true','agreement (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] = false'),
 ('dropped_entry_count','(sourceForest (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[],[2,3]]).length = 3','(sourceForest (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[],[2,3]]).length = 2'),
 ('canonical_order_assumption','sourceForest (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[3,2],[1,0]] = [.node (.leaf 0) (.leaf 1),.node (.leaf 2) (.leaf 3)]','sourceForest (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[3,2],[1,0]] = [.node (.leaf 2) (.leaf 3),.node (.leaf 0) (.leaf 1)]'),
 ('fabricated_A_zero','additionalCost groupAs fa = 0','additionalCost groupAs fa = 1'),
 ('forced_B_internal_clearance','pairwiseEmbeddings groupT [[3,5],[4,6]] = true','pairwiseEmbeddings groupT [[3,5],[4,6]] = false'),
 ('omitted_B_piece','groupBs.length = 1','groupBs.length = 2'),
 ('free_whole_B_substitution','additionalCost groupBs fbCheap = 0','additionalCost groupBs fbCheap = 1')]
false=header+'\n'.join('theorem false_'+n+' : '+bad+' := by decide\n' for n,bad,good in claims)
clean=header+'\n'.join('theorem clean_'+n+' : '+good+' := by decide\n' for n,bad,good in claims)
(F/'FreshActualFalseV1.lean').write_text(false);(F/'FreshActualCleanV1.lean').write_text(clean)
(F/'FreshDirtyScientificV1.lean').write_text('''import ResidualConsumer
namespace FreshTargetDirty
axiom unusedFalse : False
private axiom hiddenFalse : False
private theorem hiddenBad : False := hiddenFalse
theorem cleanHeadline : True := True.intro
end FreshTargetDirty
''')
# Freeze the postcontact detector inputs before executing them. They instantiate
# already-frozen false/clean expectations; no scientific expectation is revised.
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(H/'ACTUAL-DETECTOR-PIN-v1.json').write_text(json.dumps({'phase':'POST_CANDIDATE_CONTACT_SUPPLEMENT','expected_false_rejections':8,'expected_clean_twin_theorems':8,'dirty_expected_total':4,'dirty_expected_rejected':3,'dirty_expected_axioms':2,'files':{n:sha(F/n) for n in ['FreshActualFalseV1.lean','FreshActualCleanV1.lean','FreshDirtyScientificV1.lean']},'fresh_independence_credit':0},indent=2)+'\n')
u.compile('FreshActualCleanV1');log=u.compile('FreshActualFalseV1','false');assert log.count("tactic 'decide' proved that the proposition")==8,log
u.compile('FreshDirtyScientificV1');rows=u.audit('FreshDirtyScientificAuditV1',['FreshDirtyScientificV1'],['FreshDirtyScientificV1'],'FRESH_CUSTOM_OR_UNSAFE')
assert len(rows)==4 and sum(x['rejected'] for x in rows)==3 and sum(x['is_axiom'] for x in rows)==2
assert any(x['name'].startswith('_private.') and x['rejected'] for x in rows)
assert any(x['name']=='FreshTargetDirty.cleanHeadline' and not x['rejected'] for x in rows)
u.state.update(verdict='PASS_ACTUAL_FALSE_CLEAN_PRIVATE_UNUSED_CUSTOM_AXIOM_GATES',false_claims_rejected=8,clean_twin_theorems=8,source_bound_frozen_expectations_unchanged=True,post_candidate_contact_supplement=True,extra_replications=0);u.save();print(json.dumps({'verdict':u.state['verdict'],'false_claims_rejected':8,'dirty_rejected':3}))
