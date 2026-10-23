from pathlib import Path
import json,hashlib
R=Path('/Users/paurel/Documents/ChatGPT/bootscience');P=R/'research/rmaf/algorithm/verification/runtime233-2026-10-15/sol-independent/postrelease-v6';old=P.parent/'postrelease-v5';idx=json.loads((P/'LICENSE-INDEX-v6.json').read_text());sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
a='results/algorithm-universal233-source-integration-20261016T092805Z-20261016T093301576999Z';b='results/algorithm-universal233-binary-caller-final-20261016T092054Z-20261016T093820Z';c='results/algorithm-universal233-recovery-source-20261016T092054Z-20261016T092457019053Z';clean=str(P.relative_to(R))+'/clean-import'
extra=['results/algorithm-universal233-optimizer-local-20261016T085144Z-20261016T085502958188Z','results/algorithm-universal233-budget-optimization-replay-20261015T213529360638Z','results/algorithm-universal233-early-resume-20261016T083330Z-20261016T083634190186Z','results/algorithm-universal233-forest-check-root-20261015T211023Z']
# Declared C contexts are distinct; no arbitrary pool merge.
seen={};collisions=[]
for root in [c]+extra:
 for path,pin in idx.items():
  tail=path.removeprefix(root+'/')
  if path.startswith(root+'/') and '/' not in tail and path.endswith('.olean'):
   if tail in seen:collisions.append({'name':tail,'same_pin':idx[seen[tail]]==pin})
   seen[tail]=path
assert not collisions,collisions
(P/'clean-import').mkdir();original=extra[0]+'/OWBudgets.lean';assert sha(R/original)==idx[original];source=(R/original).read_text();assert source.startswith('import OWControls\n');adapted=source.replace('import OWControls\n','import OWOptimize\n',1);(P/'clean-import/OWBudgets.lean').write_text(adapted);(P/'clean-import/OWBudgets.lean').chmod(0o444)
base={'initial_subprocess_seconds':60,'disk_floor_bytes':3*1024**3,'lean_MiB':3072,'raw_cap_bytes':16*1024**2,'line_cap_bytes':16*1024**2,'compressed_budget_bytes':256*1024**2}
cleanplan=base|{'source':'clean-import/OWBudgets.lean','source_sha256':sha(P/'clean-import/OWBudgets.lean'),'original_source':original,'original_sha256':idx[original],'only_change':'line1 import OWControls -> import OWOptimize; all subsequent bytes/theorem bodies identical','roots':extra,'theorems':['OrdinaryDispatch.OptimizerLocalWork.scan_trial_budget_range','OrdinaryDispatch.OptimizerLocalWork.actual_trial_budget_cap']};(P/'CLEAN-IMPORT-PLAN-v6.json').write_text(json.dumps(cleanplan,indent=2)+'\n')
(P/'IMPORT-BINDING-v6.json').write_text(json.dumps({'A':a,'B':b,'C':c,'C_additional_roots':[clean]+extra,'C_direct_basename_collisions_except_intentional_OWBudgets_overlay':collisions,'C_overlay':'Fresh own import-only adaptation of exact OWBudgets two proof bodies, resolves before author OWBudgets/OWControls. No author control import/compile/execution. No canonical C dependency replay claim.','A_B_C_not_merged':True,'available_pins_not_actual_import_closure':True},indent=2)+'\n')
mods=[]
def add(group,root,m,ts):
 path=root+'/'+m+'.lean';assert sha(R/path)==idx[path];mods.append({'package':group+'-'+m,'module':m,'source':path,'source_sha256':idx[path],'canonical_import_root':root,'additional_import_roots':[clean]+extra if group=='recovery' else [],'theorems':ts})
A='OrdinaryDispatch.FullSourceWork.';B='GenericForest.BinaryCaller.';C='OrdinaryDispatch.RecoveryLocalWork.'
for m,ts in [('WeightedSourceSubtotal',['sourceSubtotal_eq','sourceSubtotal_bound']),('OrdinaryChildrenSource',['ordinary_run_children_value','ordinary_children_checker','childForestDebit_split','oneSource_split','highSource_split']),('ChildrenSourceBound',['childForestDebit_local_bound','oneSource_local_exponential','highSource_local_exponential']),('OrdinarySimpleTreeSource',['simpleLocalDebit_bound','simpleTreeSource_bound','prefixAndSimpleTreeSource_bound']),('Rule4CallerSource',['rule4Source_value','rule4Source_split']),('SelectedAgreementBinding',['selected_arm_closed_checker','selectedArmSource_value','selectedArmSource_split','selectedArmSource_local'])]:add('ordinary',a,m,[A+t for t in ts])
for m,ts in [('BinaryCallerSetup',['checkerCapacity_global_width','checkerCapacity_global_setup','checker_work_global']),('BinaryCallerPayload',['payBudget_caps','raw_parent_setup_paid','raw_parent_global_work','restriction_global_caps']),('BinaryCallerActual',['singleton_actual_call','disjoint_actual_call','raw_parent_actual_call','raw_parent_candidate_sizes']),('BinaryCallerOrdinaryBounds',['fast_singleton_candidate_sizes'])]:add('binary',b,m,[B+t for t in ts])
for m,ts in [('RWTree',['meterNormalize_value','meterErase_bound']),('RWChoose',['meterChoose_value','meterChoose_bound']),('RWLocal',['meterAttempt_bound','meterStep_value','meterStep_bound']),('RWRun',['meterRun_value','meterRun_bound','meterRun_closed']),('RWInitial',['meterInitial_bound','meterInitial_coloring','meterGenerate_value','meterGenerate_bound']),('RWFinal',['meterRecover_value','final_source_work_bound','final_source_uniform','final_source_absorbed']),('RWInterface',['optimizer_recovery_once_bound','optimizer_recovery_233']),('RWRefusals',['final_source_refused','generate_source_refused'])]:add('recovery',c,m,[C+t for t in ts])
plan=base|{'version':6,'scope':'18 selected exact source rechecks, separate contexts. C unchanged sources use explicit own OWBudgets import-only adaptation to avoid author controls. No full imported-body/origin/native/global acceptance.','modules':mods,'new_blind_credit':0,'own_clean_import_receipt':'CLEAN-IMPORT-RECEIPT-v6.json'};(P/'RECHECK-PLAN-v6.json').write_text(json.dumps(plan,indent=2)+'\n')
s=(old/'recheck_consumers_v5.py').read_text().replace('RECHECK-PLAN-v5.json','RECHECK-PLAN-v6.json').replace('LICENSE-INDEX-v5.json','LICENSE-INDEX-v6.json').replace('KERNEL-CONTACT-v5.jsonl','KERNEL-CONTACT-v6.jsonl').replace('selected v5 consumer','selected v6 consumer')
s=s.replace('records=[]\ntry:',"records=[]\ntry:\n    clean_receipt=json.loads((HERE/plan['own_clean_import_receipt']).read_text())\n    for rel,pin in clean_receipt['own_import_pins'].items():assert sha(HERE/rel)==pin\n")
(P/'recheck_consumers_v6.py').write_text(s)
controls={
'BaselineTrue.lean':'example : 2+3=5 := by decide +kernel\n','BaselineFalse.lean':'example : 2+3=6 := by decide +kernel\n',
'OrdinaryTruth.lean':'''import OrdinarySimpleTreeSource
import Rule4CallerSource
open RMAF OrdinaryDispatch.FullSourceWork
example : sourceSubtotal (fun _ _ _=>7) 2 (.leaf 0) (.leaf 1)=7 := by rw [sourceSubtotal_eq]; decide +kernel
example : sourceSubtotal (fun _ _ r=>r+2) 10 (.leaf 0) (.leaf 1)=12 := by rw [sourceSubtotal_eq]; decide +kernel
example : simpleLocalDebit (.leaf 0) (.leaf 1) 1000=0 := by decide +kernel
example : simpleTreeSource 7 (.leaf 0) (.leaf 0)=0 := by rw [simpleTreeSource,sourceSubtotal_eq]; decide +kernel
example : (leafAddressMeter 0 (.node (.leaf 0) (.leaf 1))).value=some [false] := by decide +kernel
example : (leafAddressMeter 0 (.node (.leaf 0) (.leaf 1))).work=8 := by decide +kernel
example : (leafAddressMeter 1 (.node (.leaf 0) (.leaf 1))).work=12 := by decide +kernel
example : (leafAddressMeter 9 (.node (.leaf 0) (.leaf 1))).value=none := by decide +kernel
''',
'OrdinaryFalse.lean':'''import WeightedSourceSubtotal
open RMAF OrdinaryDispatch.FullSourceWork
example : sourceSubtotal (fun _ _ _=>7) 2 (.leaf 0) (.leaf 1)=0 := by rw [sourceSubtotal_eq]; decide +kernel
''',
'BinaryTruth.lean':'''import BinaryCallerOrdinaryBounds
open GenericForest.BinaryProvider GenericForest.BinaryCaller GenericForest.ScalarBits
private def z : GenericForest.BinaryProvider.Tree := .leaf []
private def bad : GenericForest.BinaryProvider.Forest := [[]]
example : decode [false,true,false,true]=10 := by decide +kernel
example : (payBudget [false,true,false,true] [(),(),(),()]).value=[false,true,true,false] := by decide +kernel
example : (payBudget [false,true,false,true] [(),(),(),()]).value.length=4 := by decide +kernel
example : (flattenAnswers [(0,([]:GenericForest.BinaryProvider.Forest)),(1,[])]).work=11 := by decide +kernel
example : (checkOptional (some z) [z] [] none).work=1 := by decide +kernel
example : (disjointFinish z [z] [] (none:Option (List (Nat×GenericForest.BinaryProvider.Forest)))).work=1 := by decide +kernel
example : setupCallsWork (some z) [z] [] [bad,bad]=2*(checkerCapacity (some z) [z] [] bad).work := by decide +kernel
example : (bestCandidates (some z) [z] [] [[[[]]],[[[]]]]).value.isSome=true := by decide +kernel
''',
'BinaryWidthFalse.lean':'''import BinaryCallerPayload
example : ([true,false,false,false,false]:List Bool).length≤2 := by decide +kernel
''',
'BinaryDebitFalse.lean':'''import BinaryCallerPayload
open GenericForest.BinaryProvider GenericForest.BinaryCaller
private def z : GenericForest.BinaryProvider.Tree := .leaf []
example : setupCallsWork (some z) [z] [] [[[]],[[]]]=(checkerCapacity (some z) [z] [] [[]]).work := by decide +kernel
''',
'RecoveryTruth.lean':'''import RWRefusals
open RMAF Universal233 Universal233.CoreProgram Universal233.WholeSourceWork OrdinaryDispatch.RecoveryLocalWork
private def leafGroup (p : Vertex) (x color : Nat) : GTree := .leaf ⟨p,[x],color⟩
private def t : Tree := .node (.leaf 0) (.leaf 1)
private def dup : Tree := .node (.leaf 0) (.leaf 0)
private def color (x : Nat) : Charged Nat := ⟨x+9,5⟩
private def same : GTree := .node [] (leafGroup [false] 0 7) (leafGroup [true] 1 7)
private def mixed : GTree := .node [] (.node [false] (leafGroup [false,false] 0 0) (leafGroup [false,true] 1 1)) (.node [true] (leafGroup [true,false] 2 0) (leafGroup [true,true] 3 1))
example : (meterGroups same).value.length=2 := by decide +kernel
example : (meterGroups same).work=20 := by decide +kernel
example : (meterNormalize same).work=28 := by decide +kernel
example : (meterNormalize same).value=leafGroup [] 0 7 := by decide +kernel
example : (meterBuild color [] t).work=42 := by decide +kernel
example : (meterBuild color [] t).coloring=10 := by decide +kernel
example : (meterInitial color 100 t).value.map Prod.fst=some 1 := by decide +kernel
example : (meterInitial color 100 dup).coloring=0 := by decide +kernel
example : (meterRun 0 mixed [] []).value.childAttempts=2 := by decide +kernel
example : (meterRun 0 mixed [] []).value.outputs.length=0 := by decide +kernel
example : (meterColor [[],[2,3],[4]] 3).value=2 := by decide +kernel
example : (meterRecover (.leaf 0) [[0]]).value.isSome=true := by decide +kernel
example : (meterRecover dup [[0]]).value.isNone=true := by decide +kernel
example : (2:Rat)^3<(233/100:Rat)^3 := by decide +kernel
''',
'RecoveryBranchFalse.lean':'''import RWRefusals
open RMAF Universal233.CoreProgram OrdinaryDispatch.RecoveryLocalWork
private def g (p : Vertex) (x color : Nat) : GTree := .leaf ⟨p,[x],color⟩
private def mixed : GTree := .node [] (.node [false] (g [false,false] 0 0) (g [false,true] 1 1)) (.node [true] (g [true,false] 2 0) (g [true,true] 3 1))
example : (meterRun 0 mixed [] []).value.childAttempts=1 := by decide +kernel
''',
'RecoveryColorFalse.lean':'''import RWRefusals
open RMAF Universal233.WholeSourceWork OrdinaryDispatch.RecoveryLocalWork
example : (meterInitial (fun x=>⟨x+9,5⟩) 100 (.node (.leaf 0) (.leaf 0))).coloring=10 := by decide +kernel
'''}
# Correct intended normalized payload retains both labels, not a single group leaf label.
controls['RecoveryTruth.lean']=controls['RecoveryTruth.lean'].replace('(meterNormalize same).value=leafGroup [] 0 7','(meterNormalize same).value=GTree.leaf ⟨[],[0,1],7⟩')
(P/'own-controls').mkdir()
for name,s in controls.items():(P/'own-controls'/name).write_text(s)
fixture='''# Own phase6 hand controls, frozen before execution

Same contacted reviewer; zero blind/replication. Reuse reader and bounded Lean methods. Baseline2+3=5/false6 first. C uses own clean import-only OWBudgets proof prerequisite, then unchanged recovery source. No author control source imported or executed.

A: singleton refused callback tree has one chosen local debit7 at q2; local r+2 at q10 gives12. Malformed simpleLocalDebit=0, and identical one-leaf pretest contributes no one/high subtotal even at q7. Leaf-address root(0,1) left success has leaf4+node4=8, right success/missing sees both leaves4+4+4=12. Corruption erases actual local7. These are finite bookkeeping/control-flow controls, not an actual nontrivial one/high/Rule4 tree census or fullcounter acceptance.

B: bits[false,true,false,true] decode10. Paying4 cuts gives6 as four bits[false,true,true,false], retaining width4 above reduced singleton size. Flattening two empty answer forests pays5*2+1=11, despite zero output blocks. Optional-none/disjoint-none work1. Two identical invalid empty-block candidates each pay capacity setup; setup sum=2*one setup. Two valid zero-label singleton candidates still select an answer. Corruptions assume padded1's five stored bits fit width2, or omit one duplicate setup. Decoded cap does not imply stored width. No represented producer is constructed or certified by these continuation fixtures.

C: groups over two leaves work4+4+4*(1+1)+4=20. Homogeneous normalization costs4+4+(4*(1+1)+12)=28 and retains combined labels[0,1],origin[],color7. Building two-leaf input with coloring5 per leaf costs(5+8)*2+8*(0+1)+8=42, coloring10. Initial budget100 is clipped to one cut for two distinct leaves. Duplicate input refuses before coloring, cost contribution0. Balanced groups colors0,1,0,1 have no unique color and choose two attempts; at run budget0 both children are pruned, childAttempts2 and outputs0. Color scan [[],[2,3],[4]] on3 returns head2. Final singleton checked partition recovers; duplicate source refuses. Rational2^3<(233/100)^3 retains the exponential and tests its absorption. Corruptions omit a pruned branch or charge coloring after duplicate refusal.

New expectations are immutable before execution; any namespace/reduction fixes must preserve propositions and be versioned. False files contain one claim to be rejected specifically as false. These controls measure neither native/compiler execution nor full cost W/w. Actual recovery helper/run/final and optimizer once/absorption claims are separately rechecked at exact theorem interfaces.
''';(P/'OWN-CONTROL-SPEC-v6.md').write_text(fixture)
items=[]
for name,s in controls.items():
 group='ordinary' if name.startswith('Ordinary') else ('binary' if name.startswith('Binary') else ('recovery' if name.startswith('Recovery') else None));root={'ordinary':a,'binary':b,'recovery':c}.get(group,'');file='own-controls/'+name
 items.append({'name':name[:-5],'source':file,'source_sha256':sha(P/file),'root':root,'additional_import_roots':[clean]+extra if group=='recovery' else [],'expected':'false' if 'False' in name else 'pass','statements':s.count('example :')})
cp=base|{'version':6,'fixture':'OWN-CONTROL-SPEC-v6.md','fixture_sha256':sha(P/'OWN-CONTROL-SPEC-v6.md'),'items':items};(P/'OWN-CONTROL-PLAN-v6.json').write_text(json.dumps(cp,indent=2)+'\n')
s=(old/'run_own_controls_v5_1.py').read_text().replace('v5 controls adapter','v6 controls adapter').replace('OWN-CONTROL-PLAN-v5.1.json','OWN-CONTROL-PLAN-v6.json').replace('BASELINE-CONTROL-RECEIPT-v5.json','BASELINE-CONTROL-RECEIPT-v6.json');(P/'run_own_controls_v6.py').write_text(s)
for f in ['IMPORT-BINDING-v6.json','CLEAN-IMPORT-PLAN-v6.json','RECHECK-PLAN-v6.json','recheck_consumers_v6.py','OWN-CONTROL-SPEC-v6.md','OWN-CONTROL-PLAN-v6.json','run_own_controls_v6.py']:(P/f).chmod(0o444)
for f in (P/'own-controls').iterdir():f.chmod(0o444)
print('Frozen',len(mods),'exact source plans;',sum(len(v['theorems']) for v in mods),'reports;',sum(v['statements'] for v in items[2:] if v['expected']=='pass'),'new truths;',sum(v['statements'] for v in items[2:] if v['expected']=='false'),'false propositions.')
