import ExactWitnesses

namespace CallbackPairingAuthor

-- Proof-level occurrence indexing, not a new SOURCE evaluator.
def indexFrom {α : Type} (k : Nat) : List α → List (Nat × α)
  | [] => []
  | x::xs => (k,x)::indexFrom (k+1) xs

theorem indexFrom_project {α : Type} (k : Nat) (xs : List α) :
    (indexFrom k xs).map Prod.snd = xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => simp only [indexFrom, List.map_cons, ih]

theorem indexFrom_length {α : Type} (k : Nat) (xs : List α) :
    (indexFrom k xs).length = xs.length := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => simp only [indexFrom, List.length_cons, ih]

theorem indexFrom_bounds {α : Type} (k : Nat) (xs : List α)
    (p : Nat × α) (hp : p ∈ indexFrom k xs) :
    k ≤ p.1 ∧ p.1 < k + xs.length := by
  induction xs generalizing k with
  | nil => simp [indexFrom] at hp
  | cons x xs ih =>
    simp only [indexFrom, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp
    · have h := ih (k+1) hp
      simp only [List.length_cons]
      omega

theorem indexFrom_distinct {α : Type} (k : Nat) (xs : List α) :
    (indexFrom k xs).Pairwise (fun p r => p.1 ≠ r.1) := by
  induction xs generalizing k with
  | nil => simp [indexFrom]
  | cons x xs ih =>
    simp only [indexFrom, List.pairwise_cons]
    constructor
    · intro p hp
      have h := indexFrom_bounds (k+1) xs p hp
      omega
    · exact ih (k+1)

theorem indexFrom_sum {α : Type} (k : Nat) (xs : List α) (fee : α → Nat) :
    ((indexFrom k xs).map (fun p => fee p.2)).sum = (xs.map fee).sum := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => simp only [indexFrom, List.map_cons, List.sum_cons, ih]

open RMAF OrdinaryDispatch

-- Universal exact SOURCE sum with concrete ordinal slots, including duplicate values.
theorem indexed_counter_step (q : Nat) (T S : Tree) :
  CompleteSource.completeSourceCounter q T S =
    CompleteSource.completeLocalDebit T S q +
    ((indexFrom 0 (WorkRecursion.ordinaryStepTrace FastOrdinary.solve q T S).queries.attach).map
      (fun slot => CompleteSource.completeSourceCounter slot.2.val.2 slot.2.val.1.1 slot.2.val.1.2)).sum := by
  rw [indexFrom_sum 0 (WorkRecursion.ordinaryStepTrace FastOrdinary.solve q T S).queries.attach
    (fun pb => CompleteSource.completeSourceCounter pb.val.2 pb.val.1.1 pb.val.1.2)]
  exact counter_step q T S

-- Compiler execution checks, not an independent numerical route.
#guard (paid t s 2).isNone
#guard (GenericForest.FrontierWork.frontier paid (some t) [s] 2).length == 1
#guard WorkRecursion.forestWork paid (fun _ _ _ => 17) (some t) [s] 2 ==
  WorkRecursion.forestWork paid (fun _ _ _ => 0) (some t) [s] 2 + 17

end CallbackPairingAuthor
