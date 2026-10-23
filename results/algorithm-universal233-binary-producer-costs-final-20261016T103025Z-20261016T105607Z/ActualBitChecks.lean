import CheckerLift
namespace GenericForest.ScalarBits
open RMAF ForestState RestrictionBridge Universal233 Universal233.WholeSourceWork GenericForest.CheckCorrespondence
open GenericForest.FrontierWork

theorem payload_bits_partition (L : Nat) (T : Option Tree) (F : Forest)
 (bits : ∀x∈labels T,labelBits x≤L) (part : partitionCheck (labels T) F=true) : PayloadLabelBits L F := by
 intro x hx
 obtain ⟨B,hB,hx⟩:=List.mem_flatten.mp hx
 exact bits x (checked_label (labels T) F part hB hx)

theorem proper_input_bits (L : Nat) (T : Option Tree) (ss : List Tree)
 (proper : ForestState.proper T ss=true) (bits : ∀x∈labels T,labelBits x≤L) : InputLabelBits L T ss := by
 refine ⟨bits,?_⟩
 intro s hs x hx
 exact bits x (checked_label (labels T) (ss.map leaves) (proper_parts _ _ proper).2
  (List.mem_map.mpr ⟨s,hs,rfl⟩) hx)

theorem return_payload_bits (actual : Ordinary) (L : Nat) (T : Option Tree) (ss : List Tree) (q : Nat) (F : Forest)
 (bits : ∀x∈labels T,labelBits x≤L) (answer : solve actual T ss q=some F) : PayloadLabelBits L F := by
 have ag:=(solve_sound actual T ss q F answer).1
 exact payload_bits_partition L T F bits (agrees_parts T ss F ag).2.1

theorem binary_accepted_inspection_bound (L : Nat) (T : Option Tree) (ss : List Tree) (q : Nat) (F : Forest)
 (inputs : InputLabelBits L T ss) (payloadLabels : PayloadLabelBits L F) (payload : StatePayloadSize T F) :
 (bitAccepted (checkerWidth L T ss q) T ss q F).value=accepted T ss q F ∧
 (bitAccepted (checkerWidth L T ss q) T ss q F).work≤
 256*(L+14+8*labelBits (stateVolume T ss q+1))*inspectionBill T ss q := by
 have h:=binary_checked_inspection_bound L T ss q F inputs payloadLabels payload
 constructor
 · have value:=h.1
   simp only [bitChecked,checked] at value
   cases hb : (bitAccepted (checkerWidth L T ss q) T ss q F).value <;>
    cases ha : accepted T ss q F <;> simp [ha,hb] at value ⊢
 · have cost:=h.2;simp only [bitChecked] at cost;omega

theorem fast_binary_checked_bound (L : Nat) (T S : Tree) (q : Nat) (F : Forest)
 (proper : DepthOne.proper T S=true) (bits : ∀x∈leaves T,labelBits x≤L)
 (answer : OrdinaryDispatch.FastOrdinary.solve q T S=some F) :
 (bitChecked (checkerWidth L (some T) [S] q) (some T) [S] q F).value=checked (some T) [S] q F ∧
 (bitChecked (checkerWidth L (some T) [S] q) (some T) [S] q F).work≤
 256*(L+14+8*labelBits (stateVolume (some T) [S] q+1))*inspectionBill (some T) [S] q := by
 have pp:=proper
 simp only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq] at pp
 have inputs : InputLabelBits L (some T) [S]:=by
  refine ⟨bits,?_⟩
  intro s hs x hx
  have eq : s=S:=by simpa using hs
  subst s
  exact bits x (pp.2.mem_iff.mpr hx)
 have payload:=fast_returned_payload T S q F proper answer
 have payloadLabels : PayloadLabelBits L F:=fun x hx=>bits x (payload.1.mem_iff.mp hx)
 exact binary_checked_inspection_bound L (some T) [S] q F inputs payloadLabels
  (state_payload_ordinary_return _ fast_returned_payload T S q F proper answer)

theorem actual_raw_binary_checks_bound (actual : Ordinary) (L : Nat) (t : Tree) (ss : List Tree)
 (h : Overlap) (q : Nat) (proper : ForestState.proper (some t) ss=true)
 (bits : ∀x∈leaves t,labelBits x≤L) :
 ((recursiveCandidates actual t ss h q).map (fun F=>(bitAccepted (checkerWidth L (some t) ss q) (some t) ss q F).work)).sum≤
 (recursiveCandidates actual t ss h q).length*
  (256*(L+14+8*labelBits (stateVolume (some t) ss q+1))*inspectionBill (some t) ss q) := by
 apply LocalPolynomial.nat_sum_le_constant
 intro F hF
 obtain ⟨io,_,answer⟩:=List.mem_filterMap.mp hF
 dsimp only at answer
 split at answer
 · exact (binary_accepted_inspection_bound L (some t) ss q F
    (proper_input_bits L (some t) ss proper bits)
    (return_payload_bits actual L (some t) _ _ F bits answer)
    (state_payload_forest_return actual (some t) _ _ F answer)).2
 · contradiction
end GenericForest.ScalarBits
