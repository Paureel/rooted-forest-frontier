import ProducerSelectorFees
import ProducerCanonicalLedger
namespace OrdinaryDispatch.StoredNumeric.ProducerBinding
open RMAF GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer
open Universal233.WholeSourceWork Universal233.CoreWork

def commonSelectedPayloadFee (N B : Nat) :=commonSelectorsFee N B+commonPayloadFee N (N+1) B+8

theorem commonSelectedPayload_work (N B : Nat) (T S : GenericForest.BinaryProvider.Tree) (a b c : Bits) (p : RMAF.Vertex)
 (tc : TreeWidth B T) (sc : TreeWidth B S) (tn : treeNodes (treeValue T)≤N) (sn : treeNodes (treeValue S)≤N)
 (ac : a.length≤B) (bc : b.length≤B) (cc : c.length≤B) (pc : p.length≤N) :
 (commonSelectedPayload T S a b c p).work≤commonSelectedPayloadFee N B := by
 have sel:=commonSelectorsBits_work N B S a b c p sc sn ac bc cc pc
 have caps:=commonSelectorsBits_width B S a b c p sc cc
 have X:=subtreeLeavesBits_caps B S p sc
 have Y:=coreSelectorBits_length S a b
 have leaves:=Nat.le_trans (bitsLeaves_count S) sn
 have yn : (outsideSelectorBits S a b c).value.length≤N+1:=by
  simp only [outsideSelectorBits,appendLabels_value,List.length_append,List.length_singleton];omega
 have payload:=commonPayloadBits_work N (N+1) B T S
  (commonSelectorsBits S a b c p).value.X (commonSelectorsBits S a b c p).value.Y
  (commonSelectorsBits S a b c p).value.x (commonSelectorsBits S a b c p).value.y tn sn
  (by change (subtreeLeavesBits S p).value.length≤N+1;omega) yn tc sc caps.1 caps.2.1 caps.2.2.1 caps.2.2.2
 simp only [commonSelectedPayload,commonSelectedPayloadFee];omega

theorem buildSetup_selectors_nonempty (T S : RMAF.Tree) (X Y : List Nat) (p : RMAF.Vertex)
 (d : OrdinaryCommonSplit.Caller.Setup) (h : OrdinaryCommonSplit.Source.buildSetup T S X Y p=some d) : X≠[] ∧ Y≠[] := by
 have ids:=OrdinaryCommonSplit.Source.buildSetup_identity T S X Y p d h
 constructor
 · intro e;have hx:=d.hx;rw [ids.2.2.1,e] at hx;contradiction
 · intro e;have hy:=d.hy;rw [ids.2.2.2,e] at hy;contradiction

/-- Actual successful common setup closes the old nonempty-selector premises. -/
theorem commonSelectedPayload_checked_step (T S U V : GenericForest.BinaryProvider.Tree) (a b c : Bits)
 (bad : Universal233.Rule5FinalClassification.BadSelection) (p : RMAF.Vertex) (d : OrdinaryCommonSplit.Caller.Setup)
 (hc : decode c=bad.c) (cc : c∈leavesBits S)
 (built : OrdinaryCommonSplit.Source.buildSetup (treeValue T) (treeValue S)
  (Universal233.HardParent.subtreeLabels (treeValue S) bad.badArc)
  (Universal233.Rule5CommonSelector.outsideLabels (treeValue S) (decode a) (decode b) bad) p=some d)
 (hu : some U∈payloadTrees (commonSelectedPayload T S a b c bad.badArc).value)
 (hv : some V∈payloadTrees (commonSelectedPayload T S a b c bad.badArc).value) : OrientedStep T S U V := by
 have ne:=buildSetup_selectors_nonempty _ _ _ _ _ d built
 apply commonSelectedPayload_stored_step T S U V a b c bad.badArc cc
 · intro e;have v:=subtreeLeavesBits_value S bad.badArc;rw [sourceSubtreeLabels_eq] at v
   rw [e] at v;exact ne.1 v.symm
 · intro e;have v:=outsideSelectorBits_value S a b c
   rw [hc] at v;rw [e] at v
   exact ne.2 v.symm
 · exact hu
 · exact hv

/-- Every displayed concrete edge extends the frozen path at exactly one step.
A whole producer must still establish its semantic query membership separately. -/
theorem commonSelectedPayload_path_next (T0 S0 T S U V : GenericForest.BinaryProvider.Tree) (d : Nat)
 (path : OrientedPath T0 S0 d T S) (step : OrientedStep T S U V) : OrientedPath T0 S0 (d+1) U V :=
 OrientedPath.next path step

/-- Actual disjoint-job allocation has a polynomial temporary width after the
new entry trim. Underlying callbacks receive the further canonical allocation. -/
theorem canonical_disjoint_allocation (B N : Nat) (t : GenericForest.BinaryProvider.Tree) (ss : List GenericForest.BinaryProvider.Tree)
 (q : Bits) (js : List (Job (GenericForest.BinaryProvider.Tree×GenericForest.BinaryProvider.Tree) GenericForest.BinaryProvider.Forest))
 (tc : TreeWidth B t) (sc : SourcesWidth B ss) (sn : ss.length≤2*N) (built : (jobsBits t ss).value=some js) :
 (allocationBits (trimBudget q).value (knownBits js).value (pendingBits js).value).value.length≤decode q+4*N+3 ∧
 (trimBudget (allocationBits (trimBudget q).value (knownBits js).value (pendingBits js).value).value).value.length≤decode q := by
 constructor
 · exact disjoint_budget_width (decode q) B N t ss (trimBudget q).value tc sc (trimBudget_semantic_width q) sn js built
 · exact (scheduler_allocation_site q js).2

/-- Scalar input bounds retain both original stored widths and semantic Q. -/
def canonicalScalarWidth (B Bq N Q : Nat) :=max (markerStorageWidth B N Q) (max Bq (Q+4*N+3))
end OrdinaryDispatch.StoredNumeric.ProducerBinding
