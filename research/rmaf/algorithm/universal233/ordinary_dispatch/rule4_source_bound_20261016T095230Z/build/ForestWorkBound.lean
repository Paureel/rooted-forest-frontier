import ForestWork
namespace GenericForest
open RMAF RestrictionBridge ForestState
open Universal233 Universal233.CoreProgram Universal233.SourceCoverage

theorem rat_sum_map_le {α : Type} (L : List α) (f g : α → Rat)
    (h : ∀ x ∈ L, f x ≤ g x) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => exact Rat.le_refl
  | cons a L ih =>
    exact qadd_le_add (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem rat_sum_mul {α : Type} (L : List α) (A : Rat) (f : α → Rat) :
    (L.map (fun x => A*f x)).sum = A*(L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons,List.sum_cons,ih,Rat.mul_add]

/-- Qualified source-operation bound. LocalBillBound covers ONLY the explicitly
printed nonrecursive charge sheet and exact paid ordinary-call work. It makes
no assumption about recursive forest work, graph soundness, or compiled code. -/
theorem source_work_bound (ordinary : Tree → Tree → Nat → Option Forest)
    (ordinaryWork : Tree → Tree → Nat → Nat) (T : Option Tree) (Q : Nat) (c K : Rat)
    (hc : 2 ≤ c) (hK : 0 ≤ K) (hlocal : LocalBillBound ordinary ordinaryWork T Q c K)
    (ss : List Tree) (q : Nat) (hqQ : q ≤ Q) (hp : proper T ss = true) :
    sourceWork ordinary ordinaryWork T ss q ≤ ((q+1 : Nat) : Rat)*K*c^q := by
  induction q using Nat.strongRecOn generalizing ss with
  | ind q ih =>
    have cpos : 0 < c := by grind
    have powpos : 0 ≤ c^q := Rat.le_of_lt (Rat.pow_pos cpos)
    have hloc := hlocal ss q hqQ hp
    have base : K*c^q ≤ ((q+1 : Nat) : Rat)*K*c^q := by
      have hn' : (1 : Nat) ≤ q+1 := by omega
      have hn : (1 : Rat) ≤ ((q+1 : Nat) : Rat) := by
        simpa using (Rat.natCast_le_natCast.2 hn')
      have hm := Rat.mul_le_mul_of_nonneg_right hn (Rat.mul_nonneg hK powpos)
      simpa only [Rat.one_mul,Rat.mul_assoc] using hm
    have childBound (t : Tree) (ht : T = some t) (h : Overlap) (hh : overlap t ss = some h) :
        ((branches t ss h q).map fun io =>
          if _hd : 1 ≤ io.2.sourceCuts.length ∧ io.2.sourceCuts.length ≤ q then
            sourceWork ordinary ordinaryWork T (replace ss io.1 io.2.partition) (q-io.2.sourceCuts.length)
          else 0).sum ≤ (q : Rat)*K*c^q := by
      let A : Rat := (q : Rat)*K*c^q
      let f : Nat × Output → Rat := fun io =>
        if _hd : 1 ≤ io.2.sourceCuts.length ∧ io.2.sourceCuts.length ≤ q then
          sourceWork ordinary ordinaryWork T (replace ss io.1 io.2.partition) (q-io.2.sourceCuts.length)
        else 0
      have hA : 0 ≤ A := Rat.mul_nonneg (Rat.mul_nonneg Rat.natCast_nonneg hK) powpos
      have each (io : Nat × Output) (hio : io ∈ branches t ss h q) :
          f io ≤ A*c^(-(io.2.sourceCuts.length : Int)) := by
        have paid := branch_paid_proper t ss (by simpa [ht] using hp) h hh q io.1 io.2 hio
        have hd : 1 ≤ io.2.sourceCuts.length ∧ io.2.sourceCuts.length ≤ q := ⟨paid.1,paid.2.1⟩
        have hl : q-io.2.sourceCuts.length < q := by omega
        have hpchild : proper T (replace ss io.1 io.2.partition) = true := by simpa [ht] using paid.2.2
        have hi := ih _ hl (replace ss io.1 io.2.partition) (by omega) hpchild
        have hn : (((q-io.2.sourceCuts.length+1 : Nat) : Rat)) ≤ (q : Rat) :=
          Rat.natCast_le_natCast.2 (by omega)
        have hpw : 0 ≤ K*c^(q-io.2.sourceCuts.length) := Rat.mul_nonneg hK (Rat.le_of_lt (Rat.pow_pos cpos))
        have hmul := Rat.mul_le_mul_of_nonneg_right hn hpw
        change sourceWork ordinary ordinaryWork T (replace ss io.1 io.2.partition) (q-io.2.sourceCuts.length) ≤ _ at hi
        simp only [f,dite_eq_left hd]
        calc
          _ ≤ (((q-io.2.sourceCuts.length+1 : Nat) : Rat))*K*c^(q-io.2.sourceCuts.length) := hi
          _ ≤ (q : Rat)*K*c^(q-io.2.sourceCuts.length) := by simpa only [Rat.mul_assoc] using hmul
          _ = A*c^(-(io.2.sourceCuts.length : Int)) := by
            rw [qpow_clear c (Rat.ne_of_gt cpos) q _ paid.2.1]
            simp only [A,Rat.mul_assoc]
      have hsum := rat_sum_map_le (branches t ss h q) f
        (fun io => A*c^(-(io.2.sourceCuts.length : Int))) each
      rw [rat_sum_mul] at hsum
      have hmass := branch_mass_le_one t ss (by simpa [ht] using hp) h hh q c hc
      have hm := Rat.mul_le_mul_of_nonneg_left hmass hA
      exact Rat.le_trans hsum (by simpa only [Rat.mul_one] using hm)
    rw [sourceWork.eq_def]
    split
    · split
      · exact Rat.le_trans (by simpa only [Rat.add_zero] using hloc) base
      · exact Rat.le_trans (by simpa only [Rat.add_zero] using hloc) base
      · rename_i t ht notsingle
        split
        · exact Rat.le_trans (by simpa only [Rat.add_zero] using hloc) base
        · rename_i h hh
          have hb := childBound t rfl h hh
          have ht := qadd_le_add hloc hb
          have he : K*c^q+(q : Rat)*K*c^q = ((q+1 : Nat) : Rat)*K*c^q := by
            rw [Rat.natCast_add]
            grind
          rw [he] at ht
          exact ht
    · exact Rat.le_trans (by simpa only [Rat.add_zero] using hloc) base

end GenericForest
