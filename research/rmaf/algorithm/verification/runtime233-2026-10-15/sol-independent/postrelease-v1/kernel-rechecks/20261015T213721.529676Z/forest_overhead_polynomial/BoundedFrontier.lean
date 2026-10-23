import FrontierSupport
namespace GenericForest.FrontierSize
open RMAF ForestState Universal233 Universal233.SourceCoverage FrontierWork

/-- Only queried pairs need the callback bill; no global-size ordinary bound. -/
theorem frontier_work_bound_on_queries (ordinary : Ordinary) (W : OrdinaryWork) (T : Option Tree)
 (ss : List Tree) (q : Nat) (c D : Rat) (hc : 2≤c) (hD : 0≤D) (hp : proper T ss=true)
 (bill : ∀p r,(p,r)∈frontier ordinary T ss q → (W p.1 p.2 r:Rat)≤D*c^r) :
 queryWorkRat W (frontier ordinary T ss q)≤D*c^q := by
 have sum:=rat_sum_map_le (frontier ordinary T ss q) (fun pb=>(W pb.1.1 pb.1.2 pb.2:Rat))
  (fun pb=>D*c^pb.2) (fun pb mem=>bill pb.1 pb.2 mem)
 rw [rat_sum_mul] at sum
 exact Rat.le_trans sum (Rat.mul_le_mul_of_nonneg_left (frontier_power_bound ordinary T ss q hp c hc) hD)

/-- A finite size/budget cap, supplied only for proper ordinary pairs. -/
def SizeCappedOrdinaryBillBound (W : OrdinaryWork) (N Q : Nat) (c D : Rat) : Prop :=
 ∀t s r,(leaves t).length≤N → (leaves s).length≤N → r≤Q →
 DepthOne.proper t s=true → (W t s r:Rat)≤D*c^r

theorem frontier_work_bound_size_capped (ordinary : Ordinary) (W : OrdinaryWork) (T : Option Tree)
 (ss : List Tree) (q N Q : Nat) (c D : Rat) (hc : 2≤c) (hD : 0≤D) (hp : proper T ss=true)
 (size : (labels T).length≤N) (budget : q≤Q) (bill : SizeCappedOrdinaryBillBound W N Q c D) :
 queryWorkRat W (frontier ordinary T ss q)≤D*c^q := by
 apply frontier_work_bound_on_queries ordinary W T ss q c D hc hD hp
 intro p r mem
 have valid:=frontier_queries_proper ordinary T ss q hp p r mem
 have sizes:=frontier_query_size ordinary T ss q hp p r mem
 exact bill p.1 p.2 r (Nat.le_trans sizes.1 size) (Nat.le_trans sizes.2 size) (Nat.le_trans valid.1 budget) valid.2

theorem source_work_bound_on_queries (ordinary : Ordinary) (W : OrdinaryWork) (T : Option Tree)
 (Q : Nat) (c K D : Rat) (hc : 2<c) (hK : 0≤K) (hD : 0≤D)
 (hloc : LocalOverheadBound ordinary T Q c K) (ss : List Tree) (q : Nat) (hqQ : q≤Q) (hp : proper T ss=true)
 (bill : ∀p r,(p,r)∈frontier ordinary T ss q → (W p.1 p.2 r:Rat)≤D*c^r) :
 sourceWork ordinary W T ss q≤(D+geometric c*K)*c^q := by
 rw [source_work_split]
 have h:=qadd_le_add (forest_overhead_bound ordinary T Q c K hc hK hloc ss q hqQ hp)
  (frontier_work_bound_on_queries ordinary W T ss q c D (Rat.le_of_lt hc) hD hp bill)
 simpa only [Rat.add_mul,Rat.mul_assoc,Rat.add_comm] using h

theorem source_work_bound_size_capped (ordinary : Ordinary) (W : OrdinaryWork) (T : Option Tree)
 (N Q : Nat) (c K D : Rat) (hc : 2<c) (hK : 0≤K) (hD : 0≤D)
 (hloc : LocalOverheadBound ordinary T Q c K) (bill : SizeCappedOrdinaryBillBound W N Q c D)
 (ss : List Tree) (q : Nat) (hqQ : q≤Q) (hp : proper T ss=true) (size : (labels T).length≤N) :
 sourceWork ordinary W T ss q≤(D+geometric c*K)*c^q := by
 rw [source_work_split]
 have h:=qadd_le_add (forest_overhead_bound ordinary T Q c K hc hK hloc ss q hqQ hp)
  (frontier_work_bound_size_capped ordinary W T ss q N Q c D (Rat.le_of_lt hc) hD hp size hqQ bill)
 simpa only [Rat.add_mul,Rat.mul_assoc,Rat.add_comm] using h
end GenericForest.FrontierSize
