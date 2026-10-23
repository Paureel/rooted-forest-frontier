import NumericReach
import ReturnedPayload
import ClassifierPayload
import ELGeometry
import MaterialBounds
namespace OrdinaryDispatch.GlobalNumeric
open RMAF ForestState Universal233 Universal233.CoreWork
open GenericForest.CheckCorrespondence

/-- Nat widths, not stored representation lengths. -/
theorem labelBits_of_lt {x B : Nat} (positive : 0<B) (bound : x<2^B) : labelBits x≤B := by
 by_cases hz : x=0
 · subst x;simp only [labelBits,Nat.log2_zero];omega
 · unfold labelBits
   exact Nat.succ_le_of_lt ((Nat.log2_lt hz).2 bound)

theorem reachable_nodes (rec : Nat→Tree→Tree→Option CommonForest) (Q N M : Nat) (T0 S0 : Tree)
 (hp0 : DepthOne.proper T0 S0=true) (size0 : (leaves T0).length≤N) (cap0 : PairCap M T0 S0)
 {d T S q} (reach : Reach rec Q T0 S0 d T S q) : treeNodes T+1≤2*N ∧ treeNodes S+1≤2*N := by
 have h:=reachable_invariant rec Q N M T0 S0 hp0 size0 cap0 reach
 have tn:=treeNodes_le_twice_leaves T
 have sn:=treeNodes_le_twice_leaves S
 omega

theorem reachable_addresses (rec : Nat→Tree→Tree→Option CommonForest) (Q N M : Nat) (T0 S0 : Tree)
 (hp0 : DepthOne.proper T0 S0=true) (size0 : (leaves T0).length≤N) (cap0 : PairCap M T0 S0)
 {d T S q} (reach : Reach rec Q T0 S0 d T S q) :
 (HardParent.vertices T).length≤2*N ∧ (HardParent.vertices S).length≤2*N ∧
 (∀v,CoreGraph.Valid T v→v.length≤2*N) ∧ (∀v,CoreGraph.Valid S v→v.length≤2*N) := by
 have h:=reachable_nodes rec Q N M T0 S0 hp0 size0 cap0 reach
 rw [OrdinaryDispatch.EarlyLocalWork.vertices_length,OrdinaryDispatch.EarlyLocalWork.vertices_length]
 exact ⟨by omega,by omega,
  fun v hv=>Nat.le_trans (GenericForest.LocalPolynomial.valid_address_bound T v hv) (by omega),
  fun v hv=>Nat.le_trans (GenericForest.LocalPolynomial.valid_address_bound S v hv) (by omega)⟩

/-- All present state labels and the two extra local fresh identifiers fit the
same original-input semantic width. Padding of binary lists remains separate. -/
theorem reachable_numeric_widths (rec : Nat→Tree→Tree→Option CommonForest) (Q N L : Nat) (T0 S0 : Tree)
 (hp0 : DepthOne.proper T0 S0=true) (size0 : (leaves T0).length≤N)
 (labels0 : ∀x,x∈leaves T0++leaves S0→x<2^L)
 {d T S q} (reach : Reach rec Q T0 S0 d T S q) :
 (∀x,x∈leaves T++leaves S→labelBits x≤semanticWidth N L Q) ∧
 labelBits (OrdinaryCommonSplit.Source.labelMax (leaves T++leaves S)+2)≤semanticWidth N L Q ∧
 labelBits q≤Q+1 := by
 have bits:=reachable_label_bits rec Q N L T0 S0 hp0 size0 labels0 reach
 have cap0 : PairCap (2^L) T0 S0 :=
  ⟨fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_left _ hx)),
   fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_right _ hx))⟩
 have fresh:=reachable_builder_fresh rec Q N (2^L) T0 S0 hp0 size0 cap0 reach
 have full:=add_lt_power L (2*(Q+N)+2)
 have exponent : L+(2*(Q+N)+2)+1=semanticWidth N L Q := by unfold semanticWidth;omega
 rw [exponent] at full
 have h:=reachable_invariant rec Q N (2^L) T0 S0 hp0 size0 cap0 reach
 refine ⟨fun x hx=>labelBits_of_lt (by unfold semanticWidth;omega) (bits x hx),
  labelBits_of_lt (by unfold semanticWidth;omega) (Nat.lt_of_le_of_lt fresh full),?_⟩
 have small:=add_lt_power 0 Q
 simp only [Nat.pow_zero,Nat.add_comm 1 Q,Nat.zero_add] at small
 exact labelBits_of_lt (by omega) (by omega)
end OrdinaryDispatch.GlobalNumeric
