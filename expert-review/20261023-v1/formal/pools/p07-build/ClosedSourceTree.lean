import ClosedLocalSource
namespace OrdinaryDispatch.GlobalSourceAssembly
open RMAF ForestState Universal233 WholeSourceWork
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.Hard2SourceWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.EarlyLocalWork

/-- Every actual ordinary invocation contributes the explicit closed local
subtotal once. Uncharged handler bodies are still absent from this counter. -/
def closedSourceSubtotal (q : Nat) (T S : Tree) : Nat := sourceSubtotal closedLocalDebit q T S

theorem closedSourceSubtotal_eq (q : Nat) (T S : Tree) :
 closedSourceSubtotal q T S=closedLocalDebit T S q+
 queryWork (fun t s r=>closedSourceSubtotal r t s) (ordinaryStepTrace FastOrdinary.solve q T S).queries :=
 sourceSubtotal_eq closedLocalDebit q T S

/-- Uniform ORIGINAL N,Q are retained even after a same-q common contraction. -/
theorem closedSourceSubtotal_bound (N Q q : Nat) (T S : Tree)
 (hp : DepthOne.proper T S=true) (size : (leaves T).length≤N) (budget : q≤Q) :
 (closedSourceSubtotal q T S:Rat)≤(closedLocalPolynomial N Q:Rat)*callNodeFactor*
 ((leaves T).length+1:Nat)*Rule5ActualTrace.base^q := by
 exact sourceSubtotal_bound closedLocalDebit N Q (closedLocalPolynomial N Q) Rat.natCast_nonneg
  (closedLocalDebit_bound N Q) q T S size budget hp

def closedQueryPolynomial (n : Nat) : Nat :=closedLocalPolynomial n n*1024*(n+1)

theorem closedSourceQuery_bound (T S : Tree) (hp : DepthOne.proper T S=true) (b : Nat)
 (budget : b<(leaves T).length) :
 (closedSourceSubtotal b T S:Rat)≤(closedQueryPolynomial (leaves T).length:Rat)*(233/100:Rat)^b := by
 have h:=closedSourceSubtotal_bound (leaves T).length (leaves T).length b T S hp (Nat.le_refl _) (Nat.le_of_lt budget)
 simpa only [closedQueryPolynomial,Rat.natCast_mul,Rat.natCast_ofNat,callNodeFactor,Rule5ActualTrace.base] using h

structure PartialSourceReceipt where
 value : Option (List (List Nat))
 closedSubtotalWork : Nat

def partialSourceMeter (q : Nat) (T S : Tree) : PartialSourceReceipt :=
 ⟨(ordinaryStepTrace FastOrdinary.solve q T S).value,closedSourceSubtotal q T S⟩

theorem partialSourceMeter_value (q : Nat) (T S : Tree) :
 (partialSourceMeter q T S).value=FastOrdinary.solve q T S := ordinaryStepTrace_value q T S

theorem common_local_binding (q : Nat) {T S : Tree} (hp : DepthOne.proper T S=true)
 (pre : DepthOne.pretest01 T S=.rejected) {reverse : Bool} {c : CherryBranching.Candidate}
 (he : early T S=.common reverse c) :
 commonLocalDebit T S q=(commonBranchMeter FastOrdinary.solve (fun _ _ _=>0) q T S reverse c).work ∧
 closedLocalDebit T S q=(meterFront q T S).work+commonLocalDebit T S q := by
 simp only [closedLocalDebit,commonLocalDebit,simpleLocalDebit,rule4LocalDebit,hard2FrontLocalDebit,
  hp,ite_true,pre,he,Nat.add_zero]
 constructor <;> trivial

theorem common_exact_callback_split (W : OrdinaryWork) (q : Nat) {T S : Tree}
 (hp : DepthOne.proper T S=true) (pre : DepthOne.pretest01 T S=.rejected)
 {reverse : Bool} {c : CherryBranching.Candidate} (he : early T S=.common reverse c) :
 (commonBranchMeter FastOrdinary.solve W q T S reverse c).work=
 commonLocalDebit T S q+queryWork W (ordinaryStepTrace FastOrdinary.solve q T S).queries := by
 have selected : CherryBranching.select (Oriented reverse T S).1 (Oriented reverse T S).2=some (.common,c) := by
  simpa only [he,EarlySound] using early_sound T S
 have ready:=common_pair_ready hp selected
 rw [(common_local_binding q hp pre he).1,ordinaryStepTrace_common FastOrdinary.solve q hp pre he]
 simpa only [queryWork,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using
  commonBranchMeter_work_split FastOrdinary.solve W q T S reverse c ready.2

theorem rule4_forward_local_binding (q : Nat) {T S : Tree} (hp : DepthOne.proper T S=true)
 (pre : DepthOne.pretest01 T S=.rejected) {s : Rule4.Choice T S} (he : early T S=.rule4Forward s) :
 rule4LocalDebit T S q=(rule4Source (cutoff FastOrdinary.solve q) (fun _ _ _=>0) s q).work ∧
 closedLocalDebit T S q=(meterFront q T S).work+rule4LocalDebit T S q := by
 simp only [closedLocalDebit,commonLocalDebit,simpleLocalDebit,rule4LocalDebit,hard2FrontLocalDebit,
  hp,ite_true,pre,he,Nat.add_zero]
 constructor <;> trivial

theorem rule4_reverse_local_binding (q : Nat) {T S : Tree} (hp : DepthOne.proper T S=true)
 (pre : DepthOne.pretest01 T S=.rejected) {s : Rule4.Choice S T} (he : early T S=.rule4Reverse s) :
 rule4LocalDebit T S q=(rule4Source (cutoff FastOrdinary.solve q) (fun _ _ _=>0) s q).work ∧
 closedLocalDebit T S q=(meterFront q T S).work+rule4LocalDebit T S q := by
 simp only [closedLocalDebit,commonLocalDebit,simpleLocalDebit,rule4LocalDebit,hard2FrontLocalDebit,
  hp,ite_true,pre,he,Nat.add_zero]
 constructor <;> trivial

theorem rule4_forward_exact_callback_split (W : OrdinaryWork) (q : Nat) {T S : Tree}
 (hp : DepthOne.proper T S=true) (pre : DepthOne.pretest01 T S=.rejected)
 {s : Rule4.Choice T S} (he : early T S=.rule4Forward s) :
 (rule4Source (cutoff FastOrdinary.solve q) W s q).work=
 rule4LocalDebit T S q+queryWork W (ordinaryStepTrace FastOrdinary.solve q T S).queries := by
 rw [(rule4_forward_local_binding q hp pre he).1]
 simpa only [ordinaryStepTrace,hp,ite_true,pre,he] using rule4Source_split (cutoff FastOrdinary.solve q) W s q

theorem rule4_reverse_exact_callback_split (W : OrdinaryWork) (q : Nat) {T S : Tree}
 (hp : DepthOne.proper T S=true) (pre : DepthOne.pretest01 T S=.rejected)
 {s : Rule4.Choice S T} (he : early T S=.rule4Reverse s) :
 (rule4Source (cutoff FastOrdinary.solve q) W s q).work=
 rule4LocalDebit T S q+queryWork W (ordinaryStepTrace FastOrdinary.solve q T S).queries := by
 rw [(rule4_reverse_local_binding q hp pre he).1]
 simpa only [ordinaryStepTrace,hp,ite_true,pre,he] using rule4Source_split (cutoff FastOrdinary.solve q) W s q
end OrdinaryDispatch.GlobalSourceAssembly
