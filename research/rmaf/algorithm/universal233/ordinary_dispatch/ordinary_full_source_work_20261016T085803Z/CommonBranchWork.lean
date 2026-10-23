import CommonConstructionWork
namespace OrdinaryDispatch.FullSourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open OrdinaryDispatch.FastOrdinary

/-- Literal common branch, with a Nat-valued recursive charge at its one
actual callback. Failure is charged; expansion is charged only on success. -/
def commonBranchMeter (rec : Nat→Tree→Tree→Option (List (List Nat))) (W : OrdinaryWork)
 (q : Nat) (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate) : Charged (Option (List (List Nat))) :=
 let p:=commonPairMeter T S reverse c
 let a:=meterLeaves p.value.1;let b:=meterLeaves T
 if a.value.length<b.value.length then
  let answer:=rec q p.value.1 p.value.2
  match answer with
  | none=>⟨none,p.work+a.work+b.work+W p.value.1 p.value.2 q+8⟩
  | some F=>let e:=expandCommonMeter T S reverse c F
            ⟨some e.value,p.work+a.work+b.work+W p.value.1 p.value.2 q+e.work+8⟩
 else ⟨none,p.work+a.work+b.work+4⟩

theorem commonBranchMeter_value (rec : Nat→Tree→Tree→Option (List (List Nat))) (W : OrdinaryWork)
 (q : Nat) (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate) :
 (commonBranchMeter rec W q T S reverse c).value=
 let p:=commonPair T S reverse c
 if (leaves p.1).length<(leaves T).length then (rec q p.1 p.2).map (expandCommon T S reverse c) else none := by
 simp only [commonBranchMeter,commonPairMeter_value,meterLeaves_value]
 split
 · cases answer:rec q (commonPair T S reverse c).1 (commonPair T S reverse c).2 <;>
    simp [answer,expandCommonMeter_value]
 · rfl

theorem commonBranchMeter_work_split (rec : Nat→Tree→Tree→Option (List (List Nat))) (W : OrdinaryWork)
 (q : Nat) (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate)
 (progress : (leaves (commonPair T S reverse c).1).length<(leaves T).length) :
 (commonBranchMeter rec W q T S reverse c).work=
 (commonBranchMeter rec (fun _ _ _=>0) q T S reverse c).work+
 W (commonPair T S reverse c).1 (commonPair T S reverse c).2 q := by
 simp only [commonBranchMeter,commonPairMeter_value,meterLeaves_value,progress,ite_true]
 cases answer:rec q (commonPair T S reverse c).1 (commonPair T S reverse c).2 <;> simp only [answer] <;> omega

/-- Actual common local source bill, including guards and successful result
expansion. The callback work is the only removed summand. -/
theorem commonBranchMeter_local_bound (q : Nat) (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate)
 (hp : DepthOne.proper T S=true)
 (selected : CherryBranching.select (Oriented reverse T S).1 (Oriented reverse T S).2=some (.common,c)) :
 (commonBranchMeter FastOrdinary.solve (fun _ _ _=>0) q T S reverse c).work≤
 256*(2*(leaves T).length+1)^2 := by
 let n:=(leaves T).length
 have same:=((DepthOne.proper_iff T S).1 hp).2.2.length_eq
 have t:=treeNodes_leafCount T;have s:=treeNodes_leafCount S
 have ready:=common_pair_ready hp selected
 have smaller:=common_pair_label_count hp selected
 have pn:=treeNodes_leafCount (commonPair T S reverse c).1
 have pair:=commonPairMeter_bound T S reverse c (2*n) (by dsimp [n];omega) (by dsimp [n];omega)
 have a:=leaves_meter_square (commonPair T S reverse c).1 (2*n) (by dsimp [n];omega)
 have b:=leaves_meter_square T (2*n) (by dsimp [n];omega)
 have pos:1≤(2*n+1)^2:=Nat.one_le_pow _ _ (by omega)
 simp only [commonBranchMeter,commonPairMeter_value,meterLeaves_value,ready.2,ite_true]
 cases answer:FastOrdinary.solve q (commonPair T S reverse c).1 (commonPair T S reverse c).2 with
 | none=>dsimp only;change _≤256*(2*n+1)^2;omega
 | some F=>
  have payload:=Rule5LocalWork.closed_payload (commonPair T S reverse c).1 (commonPair T S reverse c).2 q ready.1 answer
  have pay:Rule5LocalWork.cells F≤2*n:=by dsimp [n];omega
  have expand:=expandCommonMeter_bound T S reverse c F (2*n) (by dsimp [n];omega) (by dsimp [n];omega) pay
  dsimp only
  change _≤256*(2*n+1)^2
  omega
end OrdinaryDispatch.FullSourceWork
