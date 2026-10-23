import StoredReachBridge
namespace OrdinaryDispatch.StoredNumeric.ClassifierReach
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer
open OrdinaryDispatch.StoredNumeric.ProducerBinding Universal233.WholeSourceWork Universal233.CoreWork
open OrdinaryDispatch.GlobalNumeric

/-- Simultaneous original-input caps, with physical B/Bq and semantic L/Q
separate. The event path is the precise remaining recursive-producer interface. -/
theorem bound_path_original_caps (rec : Nat→RMAF.Tree→RMAF.Tree→Option OrdinaryDispatch.CommonForest)
 (q0 : Bits) (T0 S0 : GenericForest.BinaryProvider.Tree) (N L B Bq Q : Nat)
 (qvalue : decode q0=Q) (qstored : q0.length≤Bq)
 (hp0 : Universal233.DepthOne.proper (treeValue T0) (treeValue S0)=true)
 (size0 : (RMAF.leaves (treeValue T0)).length≤N)
 (labels0 : ∀x,x∈RMAF.leaves (treeValue T0)++RMAF.leaves (treeValue S0)→x<2^L)
 (tc0 : TreeWidth B T0) (sc0 : TreeWidth B S0)
 {d T S q} (path : BoundPath rec q0 T0 S0 d T S q) :
 d≤Q+N ∧ decode q≤Q ∧ q.length≤max Bq Q ∧
 TreeWidth (stateStorageWidth B N Q) T ∧ TreeWidth (stateStorageWidth B N Q) S ∧
 treeNodes (treeValue T)≤2*N ∧ treeNodes (treeValue S)≤2*N ∧
 ∀x,x∈RMAF.leaves (treeValue T)++RMAF.leaves (treeValue S)→x<2^(semanticWidth N L Q) := by
 have pair:=bound_path_bridge rec q0 T0 S0 path
 have reach : Reach rec Q (treeValue T0) (treeValue S0) d (treeValue T) (treeValue S) (decode q):=by simpa only [qvalue] using pair.2
 have initial : PairCap (2^L) (treeValue T0) (treeValue S0):=
  ⟨fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_left _ hx)),fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_right _ hx))⟩
 have depth:=reachable_path_depth rec Q N (2^L) (treeValue T0) (treeValue S0) hp0 size0 initial reach
 have stored:=all_orientations_global_caps B N Q T0 S0 hp0 size0 tc0 sc0 pair.1 depth
 have qb:=bound_path_budget rec q0 T0 S0 path
 have qw : q.length≤max Bq Q:=by rw [qvalue] at qb;exact Nat.le_trans qb.2 (Nat.max_le.mpr ⟨Nat.le_trans qstored (Nat.le_max_left _ _),Nat.le_max_right _ _⟩)
 exact ⟨depth,by simpa only [qvalue] using qb.1,qw,stored.1,stored.2.1,stored.2.2.1,stored.2.2.2.1,
  reachable_label_bits rec Q N L (treeValue T0) (treeValue S0) hp0 size0 labels0 reach⟩

/-- At a reached actual selected cherry, both classifier fees and the selected
stored endpoints/c/address widths follow from the same event path. -/
theorem reached_classifier_contract (rec : Nat→RMAF.Tree→RMAF.Tree→Option OrdinaryDispatch.CommonForest)
 (q0 : Bits) (T0 S0 : GenericForest.BinaryProvider.Tree) (N L B Bq Q : Nat)
 (qvalue : decode q0=Q) (qstored : q0.length≤Bq)
 (hp0 : Universal233.DepthOne.proper (treeValue T0) (treeValue S0)=true)
 (size0 : (RMAF.leaves (treeValue T0)).length≤N)
 (labels0 : ∀x,x∈RMAF.leaves (treeValue T0)++RMAF.leaves (treeValue S0)→x<2^L)
 (tc0 : TreeWidth B T0) (sc0 : TreeWidth B S0)
 {d T S q} (path : BoundPath rec q0 T0 S0 d T S q)
 (p : Universal233.CherryBranching.Priority) (c : CandidateBits) (bad : BadBits)
 (selected : (selectPriorityBits T S).value=some (p,c))
 (selectedBad : (selectBadBits T S c.a c.b).value=some bad) :
 let W:=stateStorageWidth B N Q
 c.a.length≤W ∧ c.b.length≤W ∧ c.parent.length≤2*N ∧
 bad.c.length≤W ∧ bad.badArc.length≤2*N ∧ bad.singletonArc.length≤2*N ∧
 (selectPriorityBits T S).work≤selectPriorityFee (2*N) W ∧
 (selectBadBits T S c.a c.b).work≤selectBadFee (2*N) W := by
 have g:=bound_path_original_caps rec q0 T0 S0 N L B Bq Q qvalue qstored hp0 size0 labels0 tc0 sc0 path
 let W:=stateStorageWidth B N Q
 have tw : TreeWidth W T:=g.2.2.2.1
 have sw : TreeWidth W S:=g.2.2.2.2.1
 have tn : treeNodes (treeValue T)≤2*N:=g.2.2.2.2.2.1
 have sn : treeNodes (treeValue S)≤2*N:=g.2.2.2.2.2.2.1
 have cpr:=selectedPriority_provenance (2*N) T S p c tn sn selected
 have bpr:=selectedBad_caps (2*N) W T S c.a c.b bad sw sn selectedBad
 have ac : c.a.length≤W:=tw c.a cpr.1
 have bc : c.b.length≤W:=tw c.b cpr.2.1
 exact ⟨ac,bc,cpr.2.2.1,bpr.2.1,bpr.2.2.1,bpr.2.2.2,
  selectPriorityBits_work (2*N) W T S tw sw tn sn,selectBadBits_work (2*N) W T S c.a c.b tw sw tn sn ac bc⟩
end OrdinaryDispatch.StoredNumeric.ClassifierReach
