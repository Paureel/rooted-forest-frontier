import StoredReachCaps
namespace OrdinaryDispatch.StoredNumeric.ClassifierReach
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer
open OrdinaryDispatch.StoredNumeric.ProducerBinding Universal233.WholeSourceWork Universal233.CoreWork

/-- Both named source classifier projections and actual stored provenance. -/
theorem classified_inputs (N B : Nat) (T S : GenericForest.BinaryProvider.Tree)
 (p : Universal233.CherryBranching.Priority) (c : CandidateBits) (bad : BadBits)
 (tc : TreeWidth B T) (sc : TreeWidth B S) (tn : treeNodes (treeValue T)≤N) (sn : treeNodes (treeValue S)≤N)
 (sel : (selectPriorityBits T S).value=some (p,c)) (badsel : (selectBadBits T S c.a c.b).value=some bad) :
 Universal233.CherryBranching.select (treeValue T) (treeValue S)=some (p,candidateValue c) ∧
 Universal233.Rule5FinalClassification.selectBad (treeValue T) (treeValue S) (decode c.a) (decode c.b)=some (badValue bad) ∧
 c.a∈leavesBits T ∧ c.b∈leavesBits T ∧ bad.c∈leavesBits S ∧
 c.a.length≤B ∧ c.b.length≤B ∧ bad.c.length≤B ∧
 c.parent.length≤N ∧ bad.badArc.length≤N ∧ bad.singletonArc.length≤N := by
 have v:=selectPriorityBits_value T S;rw [sel] at v
 have b:=selectBadBits_value T S c.a c.b;rw [badsel] at b
 have pr:=selectedPriority_provenance N T S p c tn sn sel
 have br:=selectedBad_caps N B T S c.a c.b bad sc sn badsel
 exact ⟨v.symm,b.symm,pr.1,pr.2.1,br.1,tc c.a pr.1,tc c.b pr.2.1,br.2.1,pr.2.2.1,br.2.2.1,br.2.2.2⟩

theorem oriented_step_flip {T S U V : GenericForest.BinaryProvider.Tree} (step : OrientedStep S T U V) : OrientedStep T S U V := by
 rcases step with step|step
 · exact Or.inr step
 · exact Or.inl step

/-- Actual original ordinary budget is k-1, with no extra root marker. -/
theorem fast_bound_path_bridge (k : Nat) (q0 : Bits) (T0 S0 : GenericForest.BinaryProvider.Tree)
 (qvalue : decode q0=k-1) {d T S q}
 (path : BoundPath OrdinaryDispatch.FastOrdinary.solve q0 T0 S0 d T S q) :
 OrientedPath T0 S0 d T S ∧
 OrdinaryDispatch.GlobalNumeric.Reach OrdinaryDispatch.FastOrdinary.solve (k-1) (treeValue T0) (treeValue S0) d (treeValue T) (treeValue S) (decode q) := by
 simpa only [qvalue] using bound_path_bridge OrdinaryDispatch.FastOrdinary.solve q0 T0 S0 path
end OrdinaryDispatch.StoredNumeric.ClassifierReach
