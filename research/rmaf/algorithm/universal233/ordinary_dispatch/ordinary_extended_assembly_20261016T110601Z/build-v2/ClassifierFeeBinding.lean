import ClassifierRequestMeter
namespace Universal233.ClassifierCheckFee
open RMAF Rule5PrefixLocalWork Rule5PendantLocalWork Rule5RemainingLocalWork Rule5PaidSelector
open Rule5PaidSelector PaidLiteralDecisionWork

/-- Literal final classifier, now with the implemented checker fee. -/
def finalSourceMeter (T S : Tree) (a b : Nat) :=finalMeter checkFee T S a b

theorem final_source_value (T S : Tree) (a b : Nat) :
 (finalSourceMeter T S a b).value=Rule5FinalClassification.selectFinal T S a b :=
 final_value checkFee T S a b

theorem final_source_work (T S : Tree) (a b L : Nat)
 (tlabs : ∀x,x∈leaves T→x<2^L) (slabs : ∀x,x∈leaves S→x<2^L) :
 (finalSourceMeter T S a b).work≤finalBudget (leaves T).length (leaves S).length
  (checkCap ((leaves T).length+(leaves S).length)) := by
 exact final_work checkFee T S a b L _ tlabs slabs (check_fee_bound _ L)

/-- Every repeated classifier request keeps its original call occurrence. -/
theorem final_source_calls (T S : Tree) (a b L : Nat)
 (tlabs : ∀x,x∈leaves T→x<2^L) (slabs : ∀x,x∈leaves S→x<2^L)
 {r : CheckRequest} (mem : r∈(finalSourceMeter T S a b).calls) :
 CheckDomain ((leaves T).length+(leaves S).length) L r ∧
 checkFee r≤checkCap ((leaves T).length+(leaves S).length) := by
 have dom:=final_calls checkFee T S a b ((leaves T).length+(leaves S).length) L
  (by omega) (by omega) tlabs slabs mem
 exact ⟨dom,check_fee_bound _ L r dom⟩

/-- Existing paid builder with both distinct implemented Kc and Kl fees. -/
def paidBuilderSourceMeter (T S : Tree) (a b : Nat) :=
 paidSelectedMeter checkFee (literalFee T S a b) T S a b

theorem paid_builder_value (T S : Tree) (a b : Nat) :
 (paidBuilderSourceMeter T S a b).value=buildSelected T S a b :=
 paid_selected_value_concrete checkFee T S a b

theorem paid_builder_work (T S : Tree) (a b L : Nat)
 (tlabs : ∀x,x∈leaves T→x<2^L) (slabs : ∀x,x∈leaves S→x<2^L) :
 (paidBuilderSourceMeter T S a b).work≤paidSelectedBudget (leaves T).length (leaves S).length
  (checkCap ((leaves T).length+(leaves S).length))
  (literalBudget ((leaves T).length+(leaves S).length)) := by
 exact paid_selected_work_concrete checkFee T S a b L _ tlabs slabs (check_fee_bound _ L)

end Universal233.ClassifierCheckFee
