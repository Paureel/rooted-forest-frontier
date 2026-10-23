import OccurrenceLaws
namespace CallbackPairingAuthor

theorem indexFrom_nth {α : Type} (k : Nat) (xs : List α) (j : Nat) :
    (indexFrom k xs)[j]? = (xs[j]?).map (fun x => (k+j,x)) := by
  induction xs generalizing k j with
  | nil => simp [indexFrom]
  | cons x xs ih =>
    cases j with
    | zero => simp [indexFrom]
    | succ j =>
      simpa [indexFrom, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (k+1) j

#print axioms indexFrom_nth
end CallbackPairingAuthor
