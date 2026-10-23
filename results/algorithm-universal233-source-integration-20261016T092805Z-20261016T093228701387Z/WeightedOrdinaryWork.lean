import OrdinaryCallBound
namespace OrdinaryDispatch.FullSourceWork
open RMAF ForestState Universal233
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion

/-- Exact discounted-work reservoir over every literal ordinary invocation.
The local term c^q allows a forest bill bounded by polynomial*c^q to be summed
without multiplying a worst exponential bill by the unweighted call count. -/
def budgetTreeWork (q : Nat) (T S : Tree) : Rat :=
 Rule5ActualTrace.base^q+
 (((ordinaryStepTrace FastOrdinary.solve q T S).queries.attach).map fun pb=>
  budgetTreeWork pb.val.2 pb.val.1.1 pb.val.1.2).sum
termination_by (q,(leaves T).length)
decreasing_by exact ordinaryStepTrace_lex FastOrdinary.solve q T S _ _ pb.property

theorem budgetTreeWork_eq (q : Nat) (T S : Tree) :
 budgetTreeWork q T S=Rule5ActualTrace.base^q+
 ((ordinaryStepTrace FastOrdinary.solve q T S).queries.map fun pb=>budgetTreeWork pb.2 pb.1.1 pb.1.2).sum := by
 rw [budgetTreeWork.eq_def]
 exact congrArg (fun L : List Rat=>Rule5ActualTrace.base^q+L.sum)
  (List.attach_map_val (l:=(ordinaryStepTrace FastOrdinary.solve q T S).queries)
   (f:=fun pb : Query=>budgetTreeWork pb.2 pb.1.1 pb.1.2))

theorem rat_query_mass_bound (f : Query→Rat) (xs : List Query) (q : Nat) (D : Rat)
 (budgets : ∀p r,(p,r)∈xs→r≤q)
 (point : ∀pb,pb∈xs→f pb≤D*Rule5ActualTrace.base^pb.2) :
 (xs.map f).sum≤D*Rule5ActualTrace.base^q*Rule5ActualTrace.mass Rule5ActualTrace.base q xs := by
 have sum:=GenericForest.rat_sum_map_le xs f (fun pb=>D*Rule5ActualTrace.base^pb.2) point
 rw [GenericForest.rat_sum_mul] at sum
 change _≤D*frontierPower Rule5ActualTrace.base xs at sum
 rw [frontierPower_as_mass Rule5ActualTrace.base (by decide +kernel : 0<Rule5ActualTrace.base) q xs budgets] at sum
 simpa only [Rat.mul_assoc,Rule5ActualTrace.mass] using sum

theorem weighted_common_step (n m q : Nat) (hm : m+1=n) (X : Rat)
 (bound : X≤callNodeFactor*(m+1:Nat)*Rule5ActualTrace.base^q) :
 Rule5ActualTrace.base^q+X≤callNodeFactor*(n+1:Nat)*Rule5ActualTrace.base^q := by
 rw [hm] at bound
 have step:=Rat.mul_le_mul_of_nonneg_right callNodeFactor_properties.1
  (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q))
 simp only [Rat.one_mul] at step
 have a : X+Rule5ActualTrace.base^q≤callNodeFactor*(n:Rat)*Rule5ActualTrace.base^q+Rule5ActualTrace.base^q := Rat.add_le_add_right.mpr bound
 have b : callNodeFactor*(n:Rat)*Rule5ActualTrace.base^q+Rule5ActualTrace.base^q≤
  callNodeFactor*(n:Rat)*Rule5ActualTrace.base^q+callNodeFactor*Rule5ActualTrace.base^q := Rat.add_le_add_left.mpr step
 rw [Rat.add_comm (Rule5ActualTrace.base^q) X]
 simpa only [Rat.natCast_add,Rat.natCast_ofNat,Rat.mul_add,Rat.mul_one,Rat.add_mul] using Rat.le_trans a b

theorem weighted_paid_step (n q : Nat) (X : Rat)
 (bound : X≤callNodeFactor*(n+1:Nat)*Rule5ActualTrace.base^q*Rule5ActualTrace.gamma Rule5ActualTrace.base) :
 Rule5ActualTrace.base^q+X≤callNodeFactor*(n+1:Nat)*Rule5ActualTrace.base^q := by
 let t : Rat:=((n+1:Nat):Rat)*Rule5ActualTrace.base^q
 have np : (1:Rat)≤((n+1:Nat):Rat):=(Rat.natCast_le_natCast (a:=1) (b:=n+1)).2 (by omega)
 have powerPos : (0:Rat)≤Rule5ActualTrace.base^q:=Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q)
 have ht : Rule5ActualTrace.base^q≤t:=by simpa only [Rat.one_mul] using Rat.mul_le_mul_of_nonneg_right np powerPos
 have tpos : (0:Rat)≤t:=Rat.le_trans powerPos ht
 have absorb:=Rat.mul_le_mul_of_nonneg_right callNodeFactor_properties.2.2 tpos
 rw [Rat.add_mul,Rat.one_mul] at absorb
 have a : Rule5ActualTrace.base^q+X≤Rule5ActualTrace.base^q+callNodeFactor*(n+1:Nat)*Rule5ActualTrace.base^q*Rule5ActualTrace.gamma Rule5ActualTrace.base:=Rat.add_le_add_left.mpr bound
 have b : Rule5ActualTrace.base^q+callNodeFactor*Rule5ActualTrace.gamma Rule5ActualTrace.base*t≤t+callNodeFactor*Rule5ActualTrace.gamma Rule5ActualTrace.base*t:=Rat.add_le_add_right.mpr ht
 have eq : callNodeFactor*(n+1:Nat)*Rule5ActualTrace.base^q*Rule5ActualTrace.gamma Rule5ActualTrace.base=callNodeFactor*Rule5ActualTrace.gamma Rule5ActualTrace.base*t:=by
  unfold t
  rw [Rat.mul_assoc callNodeFactor ((n+1:Nat):Rat) (Rule5ActualTrace.base^q),
   Rat.mul_assoc callNodeFactor (((n+1:Nat):Rat)*Rule5ActualTrace.base^q) (Rule5ActualTrace.gamma Rule5ActualTrace.base),
   Rat.mul_comm (((n+1:Nat):Rat)*Rule5ActualTrace.base^q) (Rule5ActualTrace.gamma Rule5ActualTrace.base),←Rat.mul_assoc]
 rw [eq] at a
 simpa only [t,Rat.mul_assoc] using Rat.le_trans a (Rat.le_trans b absorb)

theorem budgetTreeWork_bound_aux (q n : Nat) : ∀T S : Tree,
 (leaves T).length=n→DepthOne.proper T S=true→
 budgetTreeWork q T S≤callNodeFactor*(n+1:Nat)*Rule5ActualTrace.base^q := by
 induction q using Nat.strongRecOn generalizing n with
 | ind q qih=>
  induction n using Nat.strongRecOn with
  | ind n nih=>
   intro T S hn hp
   let xs:=(ordinaryStepTrace FastOrdinary.solve q T S).queries
   have child (p : Tree×Tree) (r : Nat) (mem : (p,r)∈xs) :
    budgetTreeWork r p.1 p.2≤callNodeFactor*((leaves p.1).length+1:Nat)*Rule5ActualTrace.base^r:=by
    have b:=ordinaryStepTrace_bounds FastOrdinary.solve q hp p r mem
    by_cases eq:r=q
    · subst r;exact nih (leaves p.1).length (by have h:=b.2.2.2.2 rfl;omega) p.1 p.2 rfl b.2.1
    · exact qih r (by omega) (leaves p.1).length p.1 p.2 rfl b.2.1
   rw [budgetTreeWork_eq]
   rcases ordinaryStepTrace_common_or_paid FastOrdinary.solve q hp with common|mass
   · obtain ⟨p,queries,proper0,count⟩:=common
     have b:=child p q (by simp only [xs,queries,List.mem_cons,List.not_mem_nil,or_false])
     rw [queries]
     simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Rat.add_zero]
     exact weighted_common_step n (leaves p.1).length q (by omega) _ b
   · have point (pb : Query) (mem : pb∈xs) : budgetTreeWork pb.2 pb.1.1 pb.1.2≤callNodeFactor*(n+1:Nat)*Rule5ActualTrace.base^pb.2:=by
      have b:=ordinaryStepTrace_bounds FastOrdinary.solve q hp pb.1 pb.2 mem
      have size:((leaves pb.1.1).length+1:Nat)≤n+1:=by omega
      have scale:=Rat.mul_le_mul_of_nonneg_right
       (Rat.mul_le_mul_of_nonneg_left (Rat.natCast_le_natCast.2 size) callNodeFactor_properties.2.1)
       (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one pb.2))
      exact Rat.le_trans (child pb.1 pb.2 mem) scale
     have sum:=rat_query_mass_bound (fun pb=>budgetTreeWork pb.2 pb.1.1 pb.1.2) xs q (callNodeFactor*(n+1:Nat))
      (fun p r mem=>(ordinaryStepTrace_bounds FastOrdinary.solve q hp p r mem).1) point
     have scale:=Rat.mul_le_mul_of_nonneg_left mass
      (Rat.mul_nonneg (Rat.mul_nonneg callNodeFactor_properties.2.1 (Rat.natCast_nonneg (a:=n+1)))
       (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q)))
     exact weighted_paid_step n q _ (Rat.le_trans sum scale)

/-- Correct c^q-weighted summation theorem for the exact ordinary trace. -/
theorem budgetTreeWork_bound (q : Nat) (T S : Tree) (hp : DepthOne.proper T S=true) :
 budgetTreeWork q T S≤callNodeFactor*((leaves T).length+1:Nat)*Rule5ActualTrace.base^q :=
 budgetTreeWork_bound_aux q (leaves T).length T S rfl hp
end OrdinaryDispatch.FullSourceWork
