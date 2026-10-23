import StoredClassifierFees
import NumericReach
namespace OrdinaryDispatch.StoredNumeric.ClassifierReach
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer
open OrdinaryDispatch.StoredNumeric.ProducerBinding Universal233.WholeSourceWork Universal233.CoreWork
open OrdinaryDispatch.WorkRecursion OrdinaryDispatch.FastOrdinary

/-- Actual permitted budget constructors for the new variant. Input padding is
retained only by the literal unchanged-budget constructor. -/
inductive BudgetEdge : Bits→Bits→Prop where
 | same (q) : BudgetEdge q q
 | trim (q) : BudgetEdge q (trimBudget q).value
 | payment (q d) : BudgetEdge q (subtractCanonical q d).value
 | allocation (q k p) : BudgetEdge q (allocationCanonical q k p).value

theorem budgetEdge_caps {q r : Bits} (edge : BudgetEdge q r) :
 decode r≤decode q ∧ r.length≤max q.length (decode q) := by
 cases edge with
 | same=>exact ⟨Nat.le_refl _,Nat.le_max_left _ _⟩
 | trim=>exact ⟨by simp,Nat.le_trans (trimBudget_semantic_width q) (Nat.le_max_right _ _)⟩
 | payment d=>exact ⟨by simp,Nat.le_trans (subtractCanonical_width q d) (Nat.le_max_right _ _)⟩
 | allocation k p=>exact ⟨by simp;omega,Nat.le_trans (allocationCanonical_width q k p) (Nat.le_max_right _ _)⟩

/-- Event interface consumed by a represented recursive implementation. The
source witness is literal membership in the frozen one-step trace; it retains
failures and duplicates. Neither depth equality nor full recursion is a premise. -/
structure BoundEvent (rec : Nat→RMAF.Tree→RMAF.Tree→Option OrdinaryDispatch.CommonForest)
 (T S : GenericForest.BinaryProvider.Tree) (q : Bits) (U V : GenericForest.BinaryProvider.Tree) (r : Bits) : Prop where
 stored : OrientedStep T S U V
 source : ((treeValue U,treeValue V),decode r)∈(ordinaryStepTrace rec (decode q) (treeValue T) (treeValue S)).queries
 budget : BudgetEdge q r

inductive BoundPath (rec : Nat→RMAF.Tree→RMAF.Tree→Option OrdinaryDispatch.CommonForest)
 (q0 : Bits) (T0 S0 : GenericForest.BinaryProvider.Tree) : Nat→GenericForest.BinaryProvider.Tree→GenericForest.BinaryProvider.Tree→Bits→Prop where
 | root : BoundPath rec q0 T0 S0 0 T0 S0 q0
 | rootTrim : BoundPath rec q0 T0 S0 0 T0 S0 (trimBudget q0).value
 | next {d T S q U V r} : BoundPath rec q0 T0 S0 d T S q→BoundEvent rec T S q U V r→BoundPath rec q0 T0 S0 (d+1) U V r

/-- Same d is obtained by simultaneous induction on actual event constructors.
No equality of independently supplied depths is assumed. -/
theorem bound_path_bridge (rec : Nat→RMAF.Tree→RMAF.Tree→Option OrdinaryDispatch.CommonForest)
 (q0 : Bits) (T0 S0 : GenericForest.BinaryProvider.Tree) {d T S q} (path : BoundPath rec q0 T0 S0 d T S q) :
 OrientedPath T0 S0 d T S ∧
 OrdinaryDispatch.GlobalNumeric.Reach rec (decode q0) (treeValue T0) (treeValue S0) d (treeValue T) (treeValue S) (decode q) := by
 induction path with
 | root=>exact ⟨OrientedPath.root,OrdinaryDispatch.GlobalNumeric.Reach.root⟩
 | rootTrim=>exact ⟨OrientedPath.root,by simpa only [trimBudget_value] using (OrdinaryDispatch.GlobalNumeric.Reach.root (rec:=rec) (Q:=decode q0) (T0:=treeValue T0) (S0:=treeValue S0))⟩
 | next path event ih=>exact ⟨OrientedPath.next ih.1 event.stored,OrdinaryDispatch.GlobalNumeric.Reach.next ih.2 event.source⟩

theorem bound_path_budget (rec : Nat→RMAF.Tree→RMAF.Tree→Option OrdinaryDispatch.CommonForest)
 (q0 : Bits) (T0 S0 : GenericForest.BinaryProvider.Tree) {d T S q} (path : BoundPath rec q0 T0 S0 d T S q) :
 decode q≤decode q0 ∧ q.length≤max q0.length (decode q0) := by
 induction path with
 | root=>exact ⟨Nat.le_refl _,Nat.le_max_left _ _⟩
 | rootTrim=>exact ⟨by simp,Nat.le_trans (trimBudget_semantic_width q0) (Nat.le_max_right _ _)⟩
 | next path event ih=>
  have e:=budgetEdge_caps event.budget
  exact ⟨Nat.le_trans e.1 ih.1,Nat.le_trans e.2 (Nat.max_le.mpr ⟨ih.2,Nat.le_trans ih.1 (Nat.le_max_right _ _)⟩)⟩

def orientedStored (reverse : Bool) (T S : GenericForest.BinaryProvider.Tree) :=if reverse then (S,T) else (T,S)

@[simp] theorem orientedStored_value (reverse : Bool) (T S : GenericForest.BinaryProvider.Tree) :
 (treeValue (orientedStored reverse T S).1,treeValue (orientedStored reverse T S).2)=OrdinaryDispatch.FastOrdinary.Oriented reverse (treeValue T) (treeValue S) := by
 cases reverse <;> rfl

/-- Actual common-cherry constructor, both orientations. Selection supplies the
stored endpoints; the exact source trace supplies its one literal query. -/
theorem common_bound_event (rec : Nat→RMAF.Tree→RMAF.Tree→Option OrdinaryDispatch.CommonForest)
 (T S : GenericForest.BinaryProvider.Tree) (q : Bits) (reverse : Bool) (c : CandidateBits)
 (hp : Universal233.DepthOne.proper (treeValue T) (treeValue S)=true)
 (pre : Universal233.DepthOne.pretest01 (treeValue T) (treeValue S)=.rejected)
 (early : OrdinaryDispatch.FastOrdinary.early (treeValue T) (treeValue S)=.common reverse (candidateValue c))
 (selected : (selectPriorityBits (orientedStored reverse T S).1 (orientedStored reverse T S).2).value=some (.common,c)) :
 let pair:=(contractPairBits c.a c.b (orientedStored reverse T S).1 (orientedStored reverse T S).2).value
 BoundEvent rec T S q pair.1 pair.2 (trimBudget q).value := by
 let A:=(orientedStored reverse T S).1
 let B:=(orientedStored reverse T S).2
 have pr:=selectedPriority_provenance (treeNodes (treeValue A)+treeNodes (treeValue B)) A B .common c (by omega) (by omega) selected
 have stored : OrientedStep T S (contractPairBits c.a c.b A B).value.1 (contractPairBits c.a c.b A B).value.2:=by
  have e : StoredStep A B (contractPairBits c.a c.b A B).value.1 (contractPairBits c.a c.b A B).value.2:=
   StoredStep.common (List.mem_append_left _ pr.1) (List.mem_append_left _ pr.2.1)
  cases reverse
  · exact Or.inl e
  · exact Or.inr e
 have value:=contractPairBits_value c.a c.b A B
 have projected : (treeValue (contractPairBits c.a c.b A B).value.1,treeValue (contractPairBits c.a c.b A B).value.2)=
  commonPair (treeValue T) (treeValue S) reverse (candidateValue c):=by
  rw [value.1,value.2]
  cases reverse <;> rfl
 refine ⟨stored,?_,BudgetEdge.trim q⟩
 rw [ordinaryStepTrace_common rec (decode q) hp pre early,projected]
 simp only [trimBudget_value,List.mem_singleton]

theorem payment_bound_event (rec : Nat→RMAF.Tree→RMAF.Tree→Option OrdinaryDispatch.CommonForest)
 (T S U V : GenericForest.BinaryProvider.Tree) (q : Bits) (cuts : List RMAF.Vertex)
 (stored : OrientedStep T S U V)
 (source : ((treeValue U,treeValue V),decode q-cuts.length)∈(ordinaryStepTrace rec (decode q) (treeValue T) (treeValue S)).queries) :
 BoundEvent rec T S q U V (subtractCanonical q (spineCounter cuts).value).value := by
 exact ⟨stored,by simpa only [subtractCanonical_value,spineCounter_value] using source,BudgetEdge.payment _ _⟩

theorem classified_payload_bound_event (rec : Nat→RMAF.Tree→RMAF.Tree→Option OrdinaryDispatch.CommonForest)
 (T S U V : GenericForest.BinaryProvider.Tree) (q a b : Bits) (d : BadBits)
 (sel : (selectBadBits T S a b).value=some d) (setup : OrdinaryCommonSplit.Caller.Setup)
 (built : OrdinaryCommonSplit.Source.buildSetup (treeValue T) (treeValue S)
  (Universal233.HardParent.subtreeLabels (treeValue S) d.badArc)
  (Universal233.Rule5CommonSelector.outsideLabels (treeValue S) (decode a) (decode b) (badValue d)) d.badArc=some setup)
 (hu : some U∈payloadTrees (commonSelectedPayload T S a b d.c d.badArc).value)
 (hv : some V∈payloadTrees (commonSelectedPayload T S a b d.c d.badArc).value)
 (source : ((treeValue U,treeValue V),decode q-1)∈(ordinaryStepTrace rec (decode q) (treeValue T) (treeValue S)).queries) :
 BoundEvent rec T S q U V (subtractCanonical q [true]).value := by
 refine ⟨classified_payload_step T S U V a b d sel setup built hu hv,?_,BudgetEdge.payment _ _⟩
 simpa only [subtractCanonical_value,decode,bit,ite_true,Nat.mul_zero,Nat.add_zero] using source
end OrdinaryDispatch.StoredNumeric.ClassifierReach
