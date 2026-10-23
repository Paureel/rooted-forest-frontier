import NumericOperands
namespace OrdinaryDispatch.GlobalNumeric
open RMAF ForestState Universal233 Universal233.CoreWork
open GenericForest.CheckCorrespondence

/-- Actual initial budget is k-1; no implicit extra root marker is inserted. -/
abbrev FastReach (k : Nat) (T0 S0 : Tree) (d : Nat) (T S : Tree) (q : Nat) :=
 Reach OrdinaryDispatch.FastOrdinary.solve (k-1) T0 S0 d T S q

/-- Universal original-input semantic contract for the frozen ordinary solver. -/
theorem fast_original_caps (k N L : Nat) (T0 S0 : Tree)
 (hp0 : DepthOne.proper T0 S0=true) (size0 : (leaves T0).length≤N)
 (labels0 : ∀x,x∈leaves T0++leaves S0→x<2^L)
 {d T S q} (reach : FastReach k T0 S0 d T S q) :
 q≤k-1 ∧ (leaves T).length≤N ∧ (leaves S).length≤N ∧ d+q+(leaves T).length≤k-1+N ∧
 treeNodes T+1≤2*N ∧ treeNodes S+1≤2*N ∧
 (∀x,x∈leaves T++leaves S→labelBits x≤semanticWidth N L (k-1)) ∧
 labelBits (OrdinaryCommonSplit.Source.labelMax (leaves T++leaves S)+2)≤semanticWidth N L (k-1) ∧
 labelBits q≤k+1 := by
 have cap0 : PairCap (2^L) T0 S0 :=
  ⟨fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_left _ hx)),
   fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_right _ hx))⟩
 have h:=reachable_invariant OrdinaryDispatch.FastOrdinary.solve (k-1) N (2^L) T0 S0 hp0 size0 cap0 reach
 have nodes:=reachable_nodes OrdinaryDispatch.FastOrdinary.solve (k-1) N (2^L) T0 S0 hp0 size0 cap0 reach
 have bits:=reachable_numeric_widths OrdinaryDispatch.FastOrdinary.solve (k-1) N L T0 S0 hp0 size0 labels0 reach
 exact ⟨h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,nodes.1,nodes.2,bits.1,bits.2.1,by omega⟩

/-- Returned payloads inherit the reachable call's label cap and contain exactly
its leaves; this charges neither arbitrary callback output nor malformed input. -/
theorem reachable_fast_payload (k N L : Nat) (T0 S0 : Tree)
 (hp0 : DepthOne.proper T0 S0=true) (size0 : (leaves T0).length≤N)
 (labels0 : ∀x,x∈leaves T0++leaves S0→x<2^L)
 {d T S q} (reach : FastReach k T0 S0 d T S q) (F : Forest)
 (answer : OrdinaryDispatch.FastOrdinary.solve q T S=some F) :
 F.flatten.length≤N ∧ F.length≤N ∧ payloadBitCells F≤N*semanticWidth N L (k-1) := by
 have cap0 : PairCap (2^L) T0 S0 :=
  ⟨fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_left _ hx)),
   fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_right _ hx))⟩
 have h:=reachable_invariant OrdinaryDispatch.FastOrdinary.solve (k-1) N (2^L) T0 S0 hp0 size0 cap0 reach
 have bits:=reachable_numeric_widths OrdinaryDispatch.FastOrdinary.solve (k-1) N L T0 S0 hp0 size0 labels0 reach
 have payload:=fast_returned_payload_bit_cells T S q F (semanticWidth N L (k-1)) h.1 answer
  (fun x hx=>bits.1 x (List.mem_append_left _ hx))
 exact ⟨by omega,by omega,Nat.le_trans payload.2.2 (Nat.mul_le_mul_right _ h.2.2.1)⟩
end OrdinaryDispatch.GlobalNumeric
