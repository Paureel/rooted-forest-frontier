from pathlib import Path
import json,hashlib
R=Path('/Users/paurel/Documents/ChatGPT/bootscience');P=R/'research/rmaf/algorithm/verification/runtime233-2026-10-15/sol-independent/postrelease-v5';old=P.parent/'postrelease-v4';idx=json.loads((P/'LICENSE-INDEX-v5.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a='results/algorithm-universal233-full-source-20261016T085803Z-20261016T090439069784Z';b='results/algorithm-universal233-rule5-selected-20261016T090023Z-freeze-20261016T092100151815Z';deps='research/rmaf/algorithm/universal233/ordinary_dispatch/rule5_selected_local_work_20261016T090023Z/imports'
seen={};overlaps=[]
for root in [b,deps]:
 for path,pin in idx.items():
  tail=path.removeprefix(root+'/')
  if path.startswith(root+'/') and '/' not in tail and path.endswith('.olean'):
   if tail in seen:overlaps.append({'basename':tail,'prior':seen[tail],'current':path,'same_olean':idx[seen[tail]]==pin})
   seen[tail]=path
assert not overlaps,overlaps
binding={'A':a,'B':b,'B_dependency_root':deps,'B_direct_basename_collisions':overlaps,'A_not_combined_with_B':True,'TreeCheckMeters':{'A_source':a+'/TreeCheckMeters.lean','A_source_sha256':idx[a+'/TreeCheckMeters.lean'],'B_olean':deps+'/TreeCheckMeters.olean','B_olean_sha256':idx[deps+'/TreeCheckMeters.olean'],'A_olean_same_pin':idx[a+'/TreeCheckMeters.olean']==idx[deps+'/TreeCheckMeters.olean']},'scope':'Separate A canonical imported context and B canonical+declared dependency context. Available binary pins are not a claim of actual import closure or all-body/origin audit.'};(P/'IMPORT-BINDING-v5.json').write_text(json.dumps(binding,indent=2)+'\n')
mods=[]
def add(group,m,theorems):
 root=a if group=='weighted' else b;source=root+'/'+m+'.lean';assert sha(R/source)==idx[source]
 mods.append({'package':group+'-'+m,'module':m,'source':source,'source_sha256':idx[source],'canonical_import_root':root,'additional_import_roots':[] if group=='weighted' else [deps],'theorems':theorems})
A='OrdinaryDispatch.FullSourceWork.';B='Universal233.Rule5SelectedLocalWork.'
for m,ts in [('WeightedOrdinaryWork',['budgetTreeWork_eq','budgetTreeWork_bound','weighted_paid_step']),('PrefixSourceWork',['prefixTreeWork_eq','prefixTreeWork_bound','prefixTreeMeter_value']),('GeneralAgreementWork',['agreementMeter_value','agreementMeter_bound','measuredAgreement_K','agreement_domain_envelope']),('CommonConstructionWork',['contractMeter_bound','commonPairMeter_value','commonPairMeter_bound','expandCommonMeter_value']),('CommonBranchWork',['commonBranchMeter_value','commonBranchMeter_work_split','commonBranchMeter_local_bound']),('CommonAgreementConsumer',['reconstruct_actual_agreement','common_real_pick_work_closed_checker','common_candidate_agreement_envelope'])]:add('weighted',m,[A+t for t in ts])
for m,ts in [('SelectedRestriction',['source_forest_value','source_forest_work','pendant_child_value','pendant_child_work']),('SelectedChildrenWork',['selected_children_value','selected_children_work','selected_child_payload','selected_child_label_bits']),('ChildrenExecutionWork',['run_children_value','run_children_local','run_children_recursive','children_answer_payload']),('ForestArmBinding',['forest_arm_value','forest_arm_local','forest_arm_recursive','forest_arm_call_domain','forest_arm_check_domain'])]:add('selected',m,[B+t for t in ts])
plan={'version':5,'scope':'Ten selected exact source consumers only. Two separate canonical import contexts; no author auditor/oracle/control execution, complete dependency producer audit or global cost theorem.','initial_subprocess_seconds':60,'disk_floor_bytes':3*1024**3,'lean_MiB':3072,'raw_cap_bytes':16*1024**2,'line_cap_bytes':16*1024**2,'compressed_budget_bytes':256*1024**2,'modules':mods,'new_blind_credit':0};(P/'RECHECK-PLAN-v5.json').write_text(json.dumps(plan,indent=2)+'\n')
s=(old/'recheck_consumers_v4.py').read_text().replace('RECHECK-PLAN-v4.json','RECHECK-PLAN-v5.json').replace('LICENSE-INDEX-v4.json','LICENSE-INDEX-v5.json').replace('KERNEL-CONTACT-v4.jsonl','KERNEL-CONTACT-v5.jsonl').replace('selected v4 consumer','selected v5 consumer');(P/'recheck_consumers_v5.py').write_text(s)
controls={
'BaselineTrue.lean':'example : 2+3=5 := by decide +kernel\n',
'BaselineFalse.lean':'example : 2+3=6 := by decide +kernel\n',
'WeightedTruth.lean':'''import PrefixSourceWork
open RMAF Universal233 OrdinaryDispatch.FullSourceWork
example : budgetTreeWork 0 (.leaf 0) (.leaf 1)=1 := by rw [budgetTreeWork_eq]; decide +kernel
example : budgetTreeWork 1 (.leaf 0) (.leaf 1)=(233/100:Rat) := by rw [budgetTreeWork_eq]; decide +kernel
example : budgetTreeWork 2 (.leaf 0) (.leaf 1)=(54289/10000:Rat) := by rw [budgetTreeWork_eq]; decide +kernel
example : prefixCoefficient 0=2097152 := by decide +kernel
example : prefixCoefficient 1=1528823808 := by decide +kernel
example : prefixTreeWork 0 (.leaf 0) (.leaf 1)=prefixTreeWork 1000 (.leaf 0) (.leaf 1) := by rw [prefixTreeWork_eq,prefixTreeWork_eq]; decide +kernel
example : ([1,0,1].map (fun r=>Rule5ActualTrace.base^r)).sum=(283/50:Rat) := by decide +kernel
''',
'WeightedFalse.lean':'''import WeightedOrdinaryWork
open RMAF OrdinaryDispatch.FullSourceWork
example : budgetTreeWork 1 (.leaf 0) (.leaf 1)=(1:Rat) := by rw [budgetTreeWork_eq]; decide +kernel
''',
'CommonTruth.lean':'''import CommonBranchWork
open RMAF OrdinaryDispatch.FullSourceWork
example : (labelMaxMeter [2,8,1]).value=8 := by decide +kernel
example : (labelMaxMeter [2,8,1]).work=13 := by decide +kernel
example : (commonFreshMeter (.node (.leaf 2) (.leaf 8))).value=9 := by decide +kernel
example : (contractMeter 0 1 7 (.node (.leaf 0) (.leaf 1))).value=.leaf 7 := by decide +kernel
example : (contractMeter 0 1 7 (.node (.leaf 0) (.leaf 1))).work=24 := by decide +kernel
example : (contractMeter 0 1 7 (.node (.leaf 0) (.leaf 2))).work=28 := by decide +kernel
example : (expandBlockMeter 0 1 7 [7,2,7]).value=[0,1,2,0,1] := by decide +kernel
example : (expandBlockMeter 0 1 7 [7,2,7]).work=37 := by decide +kernel
''',
'CommonFalse.lean':'''import CommonBranchWork
open RMAF OrdinaryDispatch.FullSourceWork
example : (contractMeter 0 1 7 (.node (.leaf 0) (.leaf 2))).work=24 := by decide +kernel
''',
'AgreementTruth.lean':'''import CommonAgreementConsumer
open RMAF OrdinaryDispatch.FullSourceWork
private def t : Tree := .node (.leaf 0) (.leaf 1)
private def s : Tree := .node (.leaf 1) (.leaf 0)
example : (agreementMeter t s [[0,1]]).value=true := by decide +kernel
example : (agreementMeter t s [[0],[1]]).value=true := by decide +kernel
example : (agreementMeter t s [[0],[0],[1]]).value=false := by decide +kernel
example : (agreementMeter t s []).value=false := by decide +kernel
example : (agreementMeter t s []).work>8 := by decide +kernel
''',
'AgreementFalse.lean':'''import CommonAgreementConsumer
open RMAF OrdinaryDispatch.FullSourceWork
example : (agreementMeter (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0)) [[0],[0],[1]]).value=true := by decide +kernel
''',
'SelectedTruth.lean':'''import ForestArmBinding
open RMAF Universal233.Rule5SelectedLocalWork
private def s : Tree := .node (.leaf 0) (.leaf 1)
private def d : Universal233.Rule5FinalClassification.BadSelection := ⟨[],[],0⟩
example : (sourceForestMeter s [[0],[],[0],[8]]).value=[.leaf 0,.leaf 0] := by decide +kernel
example : (makeChildMeter s [[0],[],[0],[8]] 7).value.paid=7 := by decide +kernel
example : (excludeOneMeter 0 [0,1,0,2]).value=[1,2] := by decide +kernel
example : (excludeOneMeter 0 [0,1,0,2]).work=13 := by decide +kernel
example : (excludeTwoMeter 0 1 [0,1,0,2]).value=[2] := by decide +kernel
example : (excludeTwoMeter 0 1 [0,1,0,2]).work=17 := by decide +kernel
example : (siblingEndpointMeter s [false]).value=some 1 := by decide +kernel
example : (siblingEndpointMeter s [false]).work=12 := by decide +kernel
example : (siblingEndpointMeter s []).work=2 := by decide +kernel
example : ForestArm (.prefix .remaining) := by decide +kernel
example : ¬ForestArm (.remaining d (.one [])) := by decide +kernel
example : ¬ForestArm (.remaining d (.second [] [])) := by decide +kernel
example : (selectedChildrenMeter s 0 1 (.remaining d (.one []))).value.length=0 := by decide +kernel
''',
'SelectedFalse.lean':'''import ForestArmBinding
open RMAF Universal233.Rule5SelectedLocalWork
example : ForestArm (.remaining ⟨[],[],0⟩ (.one [])) := by decide +kernel
''',
'ForestLedgerTruth.lean':'''import ForestArmBinding
open RMAF Universal233.Rule5SelectedLocalWork
private def c : Universal233.CherryBranching.Child := ⟨[[0]],[.leaf 0],1⟩
private def no : Ordinary := fun _ _ _=>none
example : (childExecutionMeter no (fun _=>5) (.leaf 0) 3 c).calls.length=1 := by decide +kernel
example : (childExecutionMeter no (fun _=>5) (.leaf 0) 3 c).recursiveWork=5 := by decide +kernel
example : ((childExecutionMeter no (fun _=>5) (.leaf 0) 3 c).calls.map (fun j=>j.budget))=[2] := by decide +kernel
example : (childrenAnswersMeter no (fun _=>5) (.leaf 0) 3 [c,c,{c with paid:=4}]).calls.length=2 := by decide +kernel
example : (childrenAnswersMeter no (fun _=>5) (.leaf 0) 3 [c,c,{c with paid:=4}]).recursiveWork=10 := by decide +kernel
example : (childrenAnswersMeter no (fun _=>5) (.leaf 0) 3 [c,c,{c with paid:=4}]).localWork=22 := by decide +kernel
example : (bestLengthMeter (fun _=>⟨true,2⟩) [[[9]],[]]).value=some [] := by decide +kernel
example : (bestLengthMeter (fun _=>⟨true,2⟩) [[[9]],[]]).work=14 := by decide +kernel
''',
'ForestLedgerFalse.lean':'''import ForestArmBinding
open RMAF Universal233.Rule5SelectedLocalWork
private def c : Universal233.CherryBranching.Child := ⟨[[0]],[.leaf 0],1⟩
example : (childrenAnswersMeter (fun _ _ _=>none) (fun _=>5) (.leaf 0) 3 [c,c,{c with paid:=4}]).recursiveWork=5 := by decide +kernel
'''}
(P/'own-controls').mkdir()
for name,source in controls.items():(P/'own-controls'/name).write_text(source)
fixture='''# Phase5 own hand-truth controls frozen before execution

Same reviewer postcontact, zero new blind/replication. Reuse calibrated Lean true/false engine and reader. No author control source imported. Fixed small expectations here were chosen from hand evaluation of the read source bodies, before any execution or candidate scientific recheck.

Weighted: malformed unequal leaves create no ordinary child calls, so budget subtotal at q0/1/2 is1,233/100,54289/10000. PrefixCoefficient0=2097152; coefficient1=2097152*3^6=1528823808. Refused proper guard's prefix work is independent of q0 versus1000. Literal residual weights[1,0,1] sum233/100+1+233/100=283/50. Corruption erases budget weight and claims1 at q1. These are singleton and generic occurrence controls, not a nontrivial actual common-tree census.

Common: maximum of2,8,1 is8; three scalar slots4 plus base1 give13. Fresh maximum9; matched cherry contract emits7 at cost24; unmatched node has two leaf costs2+2+24=28. Expanding7,2,7 into0,1,2,0,1 costs12*3+1=37. Corruption omits child traversals in unmatched contraction and claims24. Exact failed-callback charge split is separately rechecked by its actual theorem; no author common fixture reused.

General agreement: the two-leaf swap agrees with whole block[0,1] and disjoint singleton blocks[0],[1]. Duplicate0 and empty partition refuse. Full-scan work on empty partition still exceeds8. Corruption accepts duplicate0. This tests general RMAF.agreement source values, not differently typed ForestState.agrees or native bit costs.

Selected helpers: restricting source(0,1) to blocks[0],[],[0],[8] produces two leaf0 occurrences; failures are removed but duplicates retained. Paid field7 retained. Exclude0 on0,1,0,2 yields1,2 at3*4+1=13; exclude0/1 yields2 at4*4+1=17. Left child's sibling endpoint1 uses reversal3+empty reversal1+subtree3+control5=12; root endpoint refusal costs1+1=2. ForestArm permits prefix and forbids remaining-one/second. Placeholder helper for unsupported one returns no children; this is not an actual runSelected value theorem. Corruption asserts ForestArm for one.

Forest ledger: hand child partition[0],source leaf0,paid1 at q3 yields one forest call at budget2, fee5. Two identical affordable occurrences plus paid4 refusal retain2 calls, fee10. Local source22=first4+second4+unaffordable2+base1+two receipt cells1+1+three loop slots3*3. Generic bestLength with true fee2 chooses empty over one block in list[[[9]],[]], work14=(2+1+0+0+4)+(2+1+0+4). Empty-score tie differs from common length-1 score. Corruption drops one duplicate forest debit and claims5. Forest solver internals are not evaluated to obtain these ledger projections, and no actual forest source-work bound is inferred.

Baseline2+3=5 and corrupted6 reuse prior calibration. Every negative has one false proposition and must fail specifically as false under decide +kernel. All expectations stay fixed across any namespace/reduction correction; failures retained.
'''
(P/'OWN-CONTROL-SPEC-v5.md').write_text(fixture)
items=[]
for name,source in controls.items():
 group='weighted' if name.startswith(('Weighted','Common','Agreement')) else ('selected' if not name.startswith('Baseline') else None);file='own-controls/'+name
 items.append({'name':name[:-5],'source':file,'source_sha256':sha(P/file),'root':a if group=='weighted' else (b if group else ''),'additional_import_roots':[deps] if group=='selected' else [],'expected':'false' if 'False' in name else 'pass','statements':source.count('example :')})
cp={k:v for k,v in plan.items() if k not in ['modules','scope']};cp.update({'fixture':'OWN-CONTROL-SPEC-v5.md','fixture_sha256':sha(P/'OWN-CONTROL-SPEC-v5.md'),'items':items});(P/'OWN-CONTROL-PLAN-v5.json').write_text(json.dumps(cp,indent=2)+'\n')
s=(old/'run_own_controls_v4_1.py').read_text().replace('v4 controls adapter','v5 controls adapter').replace('OWN-CONTROL-PLAN-v4.1.json','OWN-CONTROL-PLAN-v5.json').replace('BASELINE-CONTROL-RECEIPT-v4.json','BASELINE-CONTROL-RECEIPT-v5.json');(P/'run_own_controls_v5.py').write_text(s)
for f in ['IMPORT-BINDING-v5.json','RECHECK-PLAN-v5.json','recheck_consumers_v5.py','OWN-CONTROL-SPEC-v5.md','OWN-CONTROL-PLAN-v5.json','run_own_controls_v5.py']:(P/f).chmod(0o444)
for f in (P/'own-controls').iterdir():f.chmod(0o444)
print('Frozen',len(mods),'source plans;',sum(len(v['theorems']) for v in mods),'reports;',sum(v['statements'] for v in items[2:] if v['expected']=='pass'),'new truths and',sum(v['statements'] for v in items[2:] if v['expected']=='false'),'false expectations. B roots disjoint.')
