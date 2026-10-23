"""Compile concrete witness after independent replay; no parent generator imports."""
from pathlib import Path
import re,json,subprocess,time,hashlib
base=Path(__file__).resolve().parent;workspace=base.parents[5];rmaf=base.parents[3]
source=base.parents[1]/'HistoryTrace.lean';text=source.read_text()
clean=re.sub(r'/\-.*?\-/','',text,flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
assert not re.search(r'\b(sorry|axiom|native_decide|admit)\b',clean)
assert re.findall(r'^import\s+(.*)',text,re.M)==['Std']
theorems=re.findall(r'^theorem\s+(\w+)',text,re.M);assert len(theorems)==11
supplement='''
namespace FreshHistoryReview
open HistoryTrace

def leaves : T → List Nat
 | .leaf i => [i]
 | .fork l r => leaves l ++ leaves r
 | .rho u => leaves u

theorem both_initial_label_censuses :
 (leaves A0).length = 12 ∧ (leaves B0).length = 12 ∧
 (List.range 12).all (fun i => contains A0 i) = true ∧
 (List.range 12).all (fun i => contains B0 i) = true := by decide

theorem protected_a_parent_tops :
 parentSub A1 (.leaf 0) = some Top1 ∧
 parentSub A2 (.leaf 0) = some Top2 ∧
 parentSub A3 (.leaf 0) = some Top3 ∧
 parentSub A4 (.leaf 0) = some Top4 := by decide

#print axioms both_initial_label_censuses
#print axioms protected_a_parent_tops
end FreshHistoryReview
'''
audit=base/'HistoryTraceAudit.lean';audit.write_text(text+supplement)
start=time.perf_counter();run=subprocess.run([str(workspace/'bootloops-lean'),str(audit)],cwd=workspace,text=True,capture_output=True,timeout=30)
log=run.stdout+run.stderr;(rmaf/'results/thesis-runtime-repair-fresh-review-history-lean.log').write_text(log)
assert run.returncode==0,log
assert len(re.findall(r'HistoryTrace\.|FreshHistoryReview\.',log))==13,log
for ax in re.findall(r'depends on axioms: \[([^]]*)\]',log):
    assert set(x.strip() for x in ax.split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'},ax
# Deliberately corrupt the final source-history conclusion on a copy.
needle='((siblingSub B4 (leaf 0)).any fun b => contains b 3) = true := by decide'
assert needle in text
false=text.replace(needle,needle.replace('= true','= false'))
falsepath=base/'HistoryTraceFalseOutside.lean';falsepath.write_text(false)
bad=subprocess.run([str(workspace/'bootloops-lean'),str(falsepath)],cwd=workspace,text=True,capture_output=True,timeout=30)
(rmaf/'results/thesis-runtime-repair-fresh-review-history-negative.log').write_text(bad.stdout+bad.stderr);assert bad.returncode!=0
receipt={'status':'checked concrete finite witness','source':str(source.relative_to(workspace)),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'source_theorems':theorems,'supplemental_theorems':['both_initial_label_censuses','protected_a_parent_tops'],'positive_exit_code':run.returncode,'all_13_standard_axioms_only':True,'observed_nonempty_axioms':['propext'],'false_outside_copy_rejected':True,'negative_exit_code':bad.returncode,'elapsed_seconds':time.perf_counter()-start,'limits':'Explicit numeric trees, selected protected tops and phase-credit schedule; source correspondence is supported by the separate fresh physical replay and source reading, not a universal Lean source-algorithm model.'}
(rmaf/'results/thesis-runtime-repair-fresh-review-history-lean.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ('positive_exit_code','all_13_standard_axioms_only','false_outside_copy_rejected','elapsed_seconds')}))
