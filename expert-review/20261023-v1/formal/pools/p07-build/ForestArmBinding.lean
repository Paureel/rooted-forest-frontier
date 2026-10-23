import ChildrenExecutionWork
import AdmittedHandler
namespace Universal233.Rule5SelectedLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5PendantLocalWork
open CherryBranching CoreWork Rule5Classification Rule5FinalClassification Rule5OrdinaryDispatch

def ForestArm : FinalSelection→Prop
 | .prefix _=>True
 | .remaining _ (.first _ _)=>True
 | .remaining _ (.third _ _)=>True
 | _=>False

theorem selected_children_count (S : Tree) (a b : Nat) (z : FinalSelection) :
 (selectedChildrenMeter S a b z).value.length≤5 := by
 rw [selected_children_value]
 cases z with
 | «prefix» s=>cases s <;> simp [selectedForestChildren,localChildren,fiveChildren]
 | remaining d z=>cases z with
  | one q=>simp [selectedForestChildren]
  | second q r=>simp [selectedForestChildren]
  | first q r=>simp only [selectedForestChildren,Rule5SourceOrientation.firstChildren];split <;> simp
  | third q r=>simp only [selectedForestChildren,Rule5SourceOrientation.thirdChildren];split <;> simp

def forestArmMeter (actual : Ordinary) (forestFee : ForestQuery→Nat) (agreementFee : Forest→Nat)
 (T S : Tree) (a b q : Nat) (z : FinalSelection) : ChildrenReceipt :=
 let cs:=selectedChildrenMeter S a b z
 let r:=runChildrenMeter actual forestFee agreementFee T S q cs.value
 ⟨r.value,cs.work+r.localWork+2,r.recursiveWork,r.calls,r.agreementChecks⟩

theorem forest_arm_value (actual : Ordinary) (forestFee : ForestQuery→Nat) (agreementFee : Forest→Nat)
 (T S : Tree) (a b q : Nat) (z : FinalSelection) (ready : ForestArm z) :
 Result.answered (forestArmMeter actual forestFee agreementFee T S a b q z).value=runSelected actual T S a b q z := by
 simp only [forestArmMeter,run_children_value,selected_children_value]
 cases z with
 | «prefix» s=>rfl
 | remaining d z=>cases z <;> first | contradiction | rfl

def forestArmBudget (nt ns K : Nat) :=selectedChildrenBudget ns+5*(K+3*nt+16)+6

theorem forest_arm_local (actual : Ordinary) (fee : CheckRequest→Nat) (forestFee : ForestQuery→Nat) (agreementFee : Forest→Nat)
 (T S : Tree) (a b q K : Nat) {z : FinalSelection}
 (sel : (finalMeter fee T S a b).value=some z) (nt : (leaves T).Nodup)
 (checker : ∀F,F.flatten.length≤(leaves T).length →F.length≤(leaves T).length →F.flatten⊆leaves T →agreementFee F≤K) :
 (forestArmMeter actual forestFee agreementFee T S a b q z).localWork≤forestArmBudget (leaves T).length (leaves S).length K := by
 have build:=selected_children_work fee T S a b sel
 have exe:=run_children_local actual forestFee agreementFee T S q (selectedChildrenMeter S a b z).value K nt checker
 have count:=selected_children_count S a b z
 have mul:=Nat.mul_le_mul_left (K+3*(leaves T).length+16) count
 simp only [forestArmMeter,forestArmBudget]
 omega

theorem forest_arm_recursive (actual : Ordinary) (forestFee : ForestQuery→Nat) (agreementFee : Forest→Nat)
 (T S : Tree) (a b q : Nat) (z : FinalSelection) :
 (forestArmMeter actual forestFee agreementFee T S a b q z).recursiveWork=
 ((forestArmMeter actual forestFee agreementFee T S a b q z).calls.map forestFee).sum :=
 run_children_recursive actual forestFee agreementFee T S q _

/-- Every actual recursive forest occurrence has its original whole child
forest, exact residual budget/payment, and a bounded total tree-cell payload. -/
theorem forest_arm_call_domain (actual : Ordinary) (fee : CheckRequest→Nat) (forestFee : ForestQuery→Nat) (agreementFee : Forest→Nat)
 {T S : Tree} {i : RMAF.Vertex} {a b q : Nat} {z : FinalSelection}
 (ch : CherryAt T i a b) (ad : Rule5Local.admitted T S a b=true)
 (sel : (finalMeter fee T S a b).value=some z) {j : ForestQuery}
 (mem : j∈(forestArmMeter actual forestFee agreementFee T S a b q z).calls) :
 j.child∈(selectedChildrenMeter S a b z).value ∧ j.budget<q ∧ j.child.paid+j.budget=q ∧
 j.child.sourceForest.length≤(leaves S).length ∧
 (j.child.sourceForest.map treeNodes).sum≤2*(leaves S).length ∧
 (∀U,U∈j.child.sourceForest →leaves U⊆leaves S) := by
 have call:=children_answers_call actual forestFee T q (selectedChildrenMeter S a b z).value mem
 have payload:=selected_child_payload fee ch ad sel call.1
 have proper:=selected_forest_facts ch ad (by rw [←final_value fee];exact sel)
  (by rw [←selected_children_value];exact call.1)
 have pos:=proper.1.2.2.2.2
 exact ⟨call.1,by omega,by omega,by omega,payload.2.2.2.1,
  fun U hU=>(payload.2.2.2.2.2 U hU).2⟩

theorem forest_arm_check_domain (actual : Ordinary) (forestFee : ForestQuery→Nat) (agreementFee : Forest→Nat)
 (T S : Tree) (a b q L : Nat) (z : FinalSelection) (nt : (leaves T).Nodup)
 (tlabs : ∀x,x∈leaves T →x<2^L) {F : Forest}
 (mem : F∈(forestArmMeter actual forestFee agreementFee T S a b q z).agreementChecks) :
 F.flatten.length=(leaves T).length ∧ F.length≤(leaves T).length ∧
 (∀x,x∈F.flatten →x<2^L) := by
 change F∈(childrenAnswersMeter actual forestFee T q (selectedChildrenMeter S a b z).value).value at mem
 rw [children_answers_value] at mem
 have p:=children_answer_payload actual T q _ mem nt
 exact ⟨p.1,p.2.1,fun x hx=>tlabs x (p.2.2 hx)⟩
end Universal233.Rule5SelectedLocalWork
