import OrdinaryCallNodes
namespace OrdinaryDispatch.WorkRecursion
open RMAF ForestState Universal233
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration

theorem queryWork_mass_bound (W : OrdinaryWork) (xs : List Query) (q : Nat) (D : Rat)
 (positive : 0≤D) (budgets : ∀p r,(p,r)∈xs→r≤q)
 (point : ∀p r,(p,r)∈xs→(W p.1 p.2 r:Rat)≤D*Rule5ActualTrace.base^r) :
 (queryWork W xs:Rat)≤D*Rule5ActualTrace.base^q*
  Rule5ActualTrace.mass Rule5ActualTrace.base q xs := by
 rw [queryWork_cast]
 have sum := GenericForest.rat_sum_map_le xs
  (fun pb=>(W pb.1.1 pb.1.2 pb.2:Rat)) (fun pb=>D*Rule5ActualTrace.base^pb.2)
  (fun pb hm=>point pb.1 pb.2 hm)
 rw [GenericForest.rat_sum_mul] at sum
 change _≤D*frontierPower Rule5ActualTrace.base xs at sum
 rw [frontierPower_as_mass Rule5ActualTrace.base (by decide +kernel : 0<Rule5ActualTrace.base) q xs budgets] at sum
 simpa only [Rat.mul_assoc,Rule5ActualTrace.mass,queryWorkRat] using sum

theorem common_node_step (n m : Nat) (hm : m+1=n) (X : Rat) (q : Nat)
 (bound : X≤callNodeFactor*(m+1:Nat)*Rule5ActualTrace.base^q) :
 1+X≤callNodeFactor*(n+1:Nat)*Rule5ActualTrace.base^q := by
 rw [hm] at bound
 have scale := Rat.mul_le_mul_of_nonneg_right callNodeFactor_properties.1
  (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q))
 simp only [Rat.one_mul] at scale
 have step : (1:Rat)≤callNodeFactor*Rule5ActualTrace.base^q := Rat.le_trans (call_base_pow_ge_one q) scale
 have a : X+1≤callNodeFactor*(n:Rat)*Rule5ActualTrace.base^q+1 := Rat.add_le_add_right.mpr bound
 have b : callNodeFactor*(n:Rat)*Rule5ActualTrace.base^q+1≤
   callNodeFactor*(n:Rat)*Rule5ActualTrace.base^q+callNodeFactor*Rule5ActualTrace.base^q := Rat.add_le_add_left.mpr step
 rw [Rat.add_comm 1 X]
 simpa only [Rat.natCast_add,Rat.natCast_ofNat,Rat.mul_add,Rat.mul_one,Rat.add_mul] using Rat.le_trans a b

theorem paid_node_step (n q : Nat) (X : Rat)
 (bound : X≤callNodeFactor*(n+1:Nat)*Rule5ActualTrace.base^q*Rule5ActualTrace.gamma Rule5ActualTrace.base) :
 1+X≤callNodeFactor*(n+1:Nat)*Rule5ActualTrace.base^q := by
 let t : Rat := ((n+1:Nat):Rat)*Rule5ActualTrace.base^q
 have np : (1:Rat)≤((n+1:Nat):Rat) := (Rat.natCast_le_natCast (a:=1) (b:=n+1)).2 (by omega)
 have scaled := Rat.mul_le_mul_of_nonneg_left (call_base_pow_ge_one q) (Rat.natCast_nonneg (a:=n+1))
 simp only [Rat.mul_one] at scaled
 have ht : (1:Rat)≤t := Rat.le_trans np scaled
 have tpos : (0:Rat)≤t := Rat.le_trans (by decide +kernel : (0:Rat)≤1) ht
 have absorb := Rat.mul_le_mul_of_nonneg_right callNodeFactor_properties.2.2 tpos
 rw [Rat.add_mul,Rat.one_mul] at absorb
 have a : (1:Rat)+X≤1+callNodeFactor*(n+1:Nat)*Rule5ActualTrace.base^q*Rule5ActualTrace.gamma Rule5ActualTrace.base := Rat.add_le_add_left.mpr bound
 have b : (1:Rat)+callNodeFactor*Rule5ActualTrace.gamma Rule5ActualTrace.base*t≤
  t+callNodeFactor*Rule5ActualTrace.gamma Rule5ActualTrace.base*t := Rat.add_le_add_right.mpr ht
 have eq : callNodeFactor*(n+1:Nat)*Rule5ActualTrace.base^q*Rule5ActualTrace.gamma Rule5ActualTrace.base=
  callNodeFactor*Rule5ActualTrace.gamma Rule5ActualTrace.base*t := by
   unfold t
   rw [Rat.mul_assoc callNodeFactor ((n+1:Nat):Rat) (Rule5ActualTrace.base^q),
    Rat.mul_assoc callNodeFactor (((n+1:Nat):Rat)*Rule5ActualTrace.base^q) (Rule5ActualTrace.gamma Rule5ActualTrace.base),
    Rat.mul_comm (((n+1:Nat):Rat)*Rule5ActualTrace.base^q) (Rule5ActualTrace.gamma Rule5ActualTrace.base),
    ←Rat.mul_assoc]
 rw [eq] at a
 have total := Rat.le_trans a (Rat.le_trans b absorb)
 simpa only [t,Rat.mul_assoc] using total

/-- Inner induction pays for common contractions; outer induction pays for
strict-budget branches. No local-cost envelope is an induction premise. -/
theorem ordinaryCallNodes_bound_aux (q n : Nat) : ∀T S : Tree,
 (leaves T).length=n→DepthOne.proper T S=true→
 (ordinaryCallNodes q T S:Rat)≤callNodeFactor*(n+1:Nat)*Rule5ActualTrace.base^q := by
 induction q using Nat.strongRecOn generalizing n with
 | ind q qih =>
  induction n using Nat.strongRecOn with
  | ind n nih =>
   intro T S hn hp
   let xs := (ordinaryStepTrace FastOrdinary.solve q T S).queries
   have child (p : Tree×Tree) (r : Nat) (mem : (p,r)∈xs) :
    (ordinaryCallNodes r p.1 p.2:Rat)≤callNodeFactor*((leaves p.1).length+1:Nat)*Rule5ActualTrace.base^r := by
    have b := ordinaryStepTrace_bounds FastOrdinary.solve q hp p r mem
    by_cases eq : r=q
    · subst r
      exact nih (leaves p.1).length (by have h:=b.2.2.2.2 rfl;omega) p.1 p.2 rfl b.2.1
    · exact qih r (by omega) (leaves p.1).length p.1 p.2 rfl b.2.1
   rw [ordinaryCallNodes_eq,Rat.natCast_add,Rat.natCast_ofNat]
   rcases ordinaryStepTrace_common_or_paid FastOrdinary.solve q hp with common|mass
   · obtain ⟨p,queries,proper0,count⟩ := common
     have b := child p q (by simp only [xs,queries,List.mem_cons,List.not_mem_nil,or_false])
     rw [queries]
     simp only [queryWork,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
     exact common_node_step n (leaves p.1).length (by omega) _ q b
   · have point (p : Tree×Tree) (r : Nat) (mem : (p,r)∈xs) :
      (ordinaryCallNodes r p.1 p.2:Rat)≤callNodeFactor*(n+1:Nat)*Rule5ActualTrace.base^r := by
      have b := ordinaryStepTrace_bounds FastOrdinary.solve q hp p r mem
      have size : ((leaves p.1).length+1:Nat)≤n+1 := by omega
      have scale := Rat.mul_le_mul_of_nonneg_right
       (Rat.mul_le_mul_of_nonneg_left (Rat.natCast_le_natCast.2 size) callNodeFactor_properties.2.1)
       (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one r))
      exact Rat.le_trans (child p r mem) scale
     have sum := queryWork_mass_bound (fun u v r=>ordinaryCallNodes r u v) xs q
      (callNodeFactor*(n+1:Nat)) (Rat.mul_nonneg callNodeFactor_properties.2.1 Rat.natCast_nonneg)
      (fun p r mem=>(ordinaryStepTrace_bounds FastOrdinary.solve q hp p r mem).1) point
     have scale := Rat.mul_le_mul_of_nonneg_left mass
      (Rat.mul_nonneg (Rat.mul_nonneg callNodeFactor_properties.2.1 (Rat.natCast_nonneg (a:=n+1)))
       (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q)))
     exact paid_node_step n q _ (Rat.le_trans sum scale)

/-- Universal 2.33 bound for the actual ordinary callback tree. Failed and
duplicate calls are counted, as are same-q common contractions. This does
not assert a full primitive, bit or native-runtime bound. -/
theorem ordinaryCallNodes_bound (q : Nat) (T S : Tree) (hp : DepthOne.proper T S=true) :
 (ordinaryCallNodes q T S:Rat)≤callNodeFactor*((leaves T).length+1:Nat)*Rule5ActualTrace.base^q :=
 ordinaryCallNodes_bound_aux q (leaves T).length T S rfl hp
end OrdinaryDispatch.WorkRecursion
