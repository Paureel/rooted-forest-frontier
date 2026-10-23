import QuerySizes
namespace Universal233.Rule5ActualTrace
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent
open CherryBranching Rule5Local Rule5Classification Rule5FinalClassification
open GenericForest.FrontierWork

theorem common_raw_nonrefusal (actual : Ordinary) {T S : Tree} {i edge : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (sel : selectFinal T S a b=some (.remaining d (.one edge))) (q : Nat) :
 ∃answer,(commonTrace actual T S a b d q).value=some answer := by
 rw [common_value]
 exact Rule5CommonSelector.selected_one_nonrefusal ch ad sel q actual

theorem queryWork_cast (W : OrdinaryWork) (xs : List Query) :
 (queryWork W xs:Rat)=(xs.map fun pb => (W pb.1.1 pb.1.2 pb.2:Rat)).sum := by
 induction xs with
 | nil => rfl
 | cons x xs ih =>
   change ((W x.1.1 x.1.2 x.2+queryWork W xs:Nat):Rat)=_
   rw [Rat.natCast_add,ih]
   rfl

/-- Only the actual emitted source-level ordinary calls need a supplied
recursive charge. The trace's mass and proper/strict/size bounds are proved,
not fields of this bill. Nonrecursive source and bit work stay separate. -/
theorem dispatch_ordinary_work_bound (actual : Ordinary) (W : OrdinaryWork)
 {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) (q : Nat) (D : Rat) (hD : 0≤D)
 (bill : ∀p r,(p,r)∈queries actual (dispatchTrace actual T S a b q).calls →
   (W p.1 p.2 r:Rat)≤D*base^r) :
 (ordinaryWork actual W (dispatchTrace actual T S a b q):Rat)≤D*base^q*gamma base := by
 let xs := queries actual (dispatchTrace actual T S a b q).calls
 have point (pb : Query) (mem : pb∈xs) : (W pb.1.1 pb.1.2 pb.2:Rat)≤D*base^pb.2 := bill pb.1 pb.2 mem
 have sum := GenericForest.rat_sum_map_le xs
   (fun pb => (W pb.1.1 pb.1.2 pb.2:Rat)) (fun pb => D*base^pb.2) point
 rw [GenericForest.rat_sum_mul] at sum
 have power := frontierPower_as_mass base (by decide +kernel : 0<base) q xs
   (fun p r mem => by have b:=dispatch_query_bounds actual ch ad q mem;omega)
 have massBound := dispatch_mass actual ch ad q
 have pos : 0≤D*base^q := Rat.mul_nonneg hD (Rat.le_of_lt (Rat.pow_pos (by decide +kernel : 0<base)))
 have scale := Rat.mul_le_mul_of_nonneg_left massBound pos
 have total : (xs.map fun pb => (W pb.1.1 pb.1.2 pb.2:Rat)).sum≤D*base^q*gamma base := by
   change _≤D*base^q*gamma base
   change _≤D*frontierPower base xs at sum
   rw [power] at sum
   exact Rat.le_trans sum (by simpa [Rat.mul_assoc,xs,mass] using scale)
 simpa [ordinaryWork,queryWork_cast,xs] using total
end Universal233.Rule5ActualTrace
