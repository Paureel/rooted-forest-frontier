import BadClassifierWork
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork CherryBranching Rule5FinalClassification

/-- The source tests outsideCheck twice for the two u/v lets. Each is paid.
Only the second paint follows the literal Boolean short-circuit. -/
def boundaryMeter (T : Tree) (X : List Nat) (c : Nat) : Measured (Option BoundarySelection) :=
 let i:=incidentMeter T X
 match i.value with
 | [q]=>⟨some (.one q),i.work+3⟩
 | [q,r]=>
  let ou:=outsideCheckMeter T X q c
  let u:=if ou.value then q else r
  let ov:=outsideCheckMeter T X q c
  let v:=if ov.value then r else q
  let p:=paintMeter T X u
  if p.value then ⟨some (.third u v),i.work+ou.work+ov.work+p.work+7⟩ else
   let s:=paintMeter T X v
   ⟨if s.value then some (.first u v) else some (.second u v),i.work+ou.work+ov.work+p.work+s.work+8⟩
 | _=>⟨none,i.work+2⟩

theorem boundary_value (T : Tree) (X : List Nat) (c : Nat) :
 (boundaryMeter T X c).value=selectBoundary T X c := by
 simp only [boundaryMeter,selectBoundary,incident_value]
 generalize hi : Rule5Local.incident T X=xs
 cases xs with
 | nil=>rfl
 | cons q qs=>cases qs with
  | nil=>rfl
  | cons r rs=>cases rs with
   | cons z zs=>rfl
   | nil=>
    simp only [outside_check_value,paint_value]
    cases ho : outsideCheck T X q c <;> simp only [ho,Bool.false_eq_true,ite_false,ite_true,paint_value]
    all_goals cases hp : Rule5Local.paint T X q <;> cases hr : Rule5Local.paint T X r <;> simp_all

def boundaryBudget (k n : Nat) :=incidentBudget k n+2*outsideCheckBudget k n+2*paintBudget k n+10

theorem boundary_work (T : Tree) (X : List Nat) (c : Nat) :
 (boundaryMeter T X c).work≤boundaryBudget X.length (leaves T).length := by
 have i:=incident_work T X
 have dom:=incident_domain T X
 simp only [boundaryMeter]
 split
 · dsimp only;unfold boundaryBudget;omega
 · rename_i q r hi
   have qc : q.length≤(leaves T).length := by have:=dom.2 q (by rw [hi];simp);omega
   have rc : r.length≤(leaves T).length := by have:=dom.2 r (by rw [hi];simp);omega
   have o:=outside_check_work T X q c qc
   have p:=paint_work T X q qc
   have s:=paint_work T X r rc
   cases ho : (outsideCheckMeter T X q c).value <;>
    simp only [ho,Bool.false_eq_true,ite_false,ite_true]
   all_goals cases hp : (paintMeter T X q).value <;> cases hr : (paintMeter T X r).value <;>
    simp only [hp,hr,Bool.false_eq_true,ite_false,ite_true] <;> unfold boundaryBudget <;> omega
 · dsimp only;unfold boundaryBudget;omega

/-- Every returned original address is bounded even when selection occurs on
non-admitted, duplicate-label or otherwise refused inputs. -/
theorem boundary_addresses (T : Tree) (X : List Nat) (c : Nat) {z : BoundarySelection}
 (sel : (boundaryMeter T X c).value=some z) :
 match z with
 | .one q=>q.length≤(leaves T).length
 | .first q r | .second q r | .third q r=>q.length≤(leaves T).length ∧ r.length≤(leaves T).length := by
 have dom:=incident_domain T X
 rw [boundary_value] at sel
 unfold selectBoundary at sel
 split at sel
 · rename_i q hi
   cases Option.some.inj sel
   have:=dom.2 q (by rw [incident_value,hi];simp)
   omega
 · rename_i q r hi
   have qc : q.length≤(leaves T).length := by have:=dom.2 q (by rw [incident_value,hi];simp);omega
   have rc : r.length≤(leaves T).length := by have:=dom.2 r (by rw [incident_value,hi];simp);omega
   cases ho : outsideCheck T X q c <;>
    cases hp : Rule5Local.paint T X q <;> cases hr : Rule5Local.paint T X r <;>
    simp only [ho,hp,hr,Bool.false_eq_true,ite_false,ite_true] at sel <;>
    cases Option.some.inj sel <;> first | exact ⟨qc,rc⟩ | exact ⟨rc,qc⟩
 · contradiction
end Universal233.Rule5PendantLocalWork
