import SelectedTrace
namespace Universal233.Rule5ActualTrace
open RMAF ForestState GenericForest.FrontierWork Universal233.PaidQueries

def mass (c : Rat) (q : Nat) (xs : List Query) : Rat := actualQueryMass c q (xs.map Prod.snd)
def debit (c : Rat) (d : Nat) : Rat := c^(-(d:Int))

theorem mass_nonnegative (c : Rat) (cp : 0<c) (q : Nat) (xs : List Query) : 0≤mass c q xs := by
 induction xs with
 | nil => simp [mass,actualQueryMass]
 | cons x xs ih =>
   simp only [mass,actualQueryMass,List.map_cons,List.sum_cons] at *
   exact Rat.add_nonneg (Rat.le_of_lt (Rat.zpow_pos cp)) ih

theorem mass_append (c : Rat) (q : Nat) (xs ys : List Query) :
 mass c q (xs++ys)=mass c q xs+mass c q ys := by simp [mass,actualQueryMass,List.map_append,List.sum_append]

theorem mass_flatMap {A : Type} (c : Rat) (q : Nat) (L : List A) (f : A→List Query) :
 mass c q (L.flatMap f)=(L.map fun a => mass c q (f a)).sum := by
 induction L with
 | nil => rfl
 | cons a L ih => simp [List.flatMap_cons,mass_append,ih]

theorem mass_lift (c : Rat) (cp : 0<c) {q r : Nat} (rq : r≤q) (xs : List Query)
 (bounds : ∀x,x∈xs →x.2≤r) : mass c q xs=debit c (q-r)*mass c r xs := by
 induction xs with
 | nil => simp [mass,actualQueryMass]
 | cons x xs ih =>
   have xb := bounds x (by simp)
   have tail := ih (fun y hy => bounds y (by simp [hy]))
   have eq : -((q-x.2:Nat):Int)= -((q-r:Nat):Int)+ -((r-x.2:Nat):Int) := by omega
   simp only [mass,actualQueryMass,List.map_cons,List.sum_cons] at *
   rw [eq,Rat.zpow_add (Rat.ne_of_gt cp),tail]
   simp only [debit,Rat.mul_add]

theorem forest_mass_paid (actual : Ordinary) (T : Option Tree) (ss : List Tree) {q r : Nat}
 (rq : r≤q) (proper : ForestState.proper T ss=true) (c : Rat) (hc : 2≤c) :
 mass c q (frontier actual T ss r)≤debit c (q-r) := by
 have cp : 0<c := by grind
 rw [mass_lift c cp rq _ (fun j hj => (frontier_queries_proper actual T ss r proper j.1 j.2 hj).1)]
 have bound := frontier_mass_bound actual T ss r proper c hc
 have lifted := Rat.mul_le_mul_of_nonneg_left bound (Rat.le_of_lt (Rat.zpow_pos (a:=c) (n:= -((q-r:Nat):Int)) cp))
 simpa [mass,debit,Rat.mul_one] using lifted

theorem current_mass_paid (actual : Ordinary) (T : Option Tree) (ss : List Tree) {q r : Nat}
 (rq : r≤q) (proper : ForestState.proper T ss=true) (c : Rat) (hc : 2≤c) :
 mass c q (currentFrontier actual T ss r)≤debit c (q-r) := by
 cases pre : ForestPretest01.pretest01 T ss with
 | refused => simp [currentFrontier,pre,mass,actualQueryMass];exact Rat.le_of_lt (Rat.zpow_pos (by grind : 0<c))
 | found F => simp [currentFrontier,pre,mass,actualQueryMass];exact Rat.le_of_lt (Rat.zpow_pos (by grind : 0<c))
 | rejected =>
   by_cases small : r≤1
   · simp [currentFrontier,pre,small,mass,actualQueryMass];exact Rat.le_of_lt (Rat.zpow_pos (by grind : 0<c))
   · simpa [currentFrontier,pre,small] using forest_mass_paid actual T ss rq proper c hc
end Universal233.Rule5ActualTrace
