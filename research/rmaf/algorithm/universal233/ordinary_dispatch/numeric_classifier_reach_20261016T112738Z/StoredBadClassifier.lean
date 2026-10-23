import StoredCherryClassifier
namespace OrdinaryDispatch.StoredNumeric.ClassifierReach
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer
open OrdinaryDispatch.StoredNumeric.ProducerBinding Universal233.WholeSourceWork Universal233.CoreWork

/-- Projection only; the executable call below remains the existing finite-bit
restriction evaluator and pays its complete scan/comparison/copy work. -/
theorem restrictionAgreesStored_value (T S : GenericForest.BinaryProvider.Tree) (X : Block) :
 (restrictionAgreesLabels T S X).value=RMAF.restrictionAgrees (treeValue T) (treeValue S) (blockValue X) := by
 let C:=(checkerCapacity (some T) [S] [] [X]).value
 have r:=checkerCapacity_ready (some T) [S] [] [X]
 exact (restrictionAgreesLabels_projects C.length T S X (r.target T (by simp)) (r.sources S (by simp)) (r.forest X (by simp))).1.trans (GenericForest.CheckCorrespondence.meterRestrictionAgrees_value _ _ _)

structure BadBits where
 badArc : RMAF.Vertex
 singletonArc : RMAF.Vertex
 c : Bits
 deriving Repr

def badValue (d : BadBits) : Universal233.Rule5FinalClassification.BadSelection :=⟨d.badArc,d.singletonArc,decode d.c⟩

def badAtBits (T S : GenericForest.BinaryProvider.Tree) (e f : RMAF.Vertex) : Charged (Option BadBits) :=
 let eq:=meterAddressEq e f
 if eq.value then ⟨none,eq.work+4⟩ else
  let X:=subtreeLeavesBits S e;let ag:=restrictionAgreesLabels T S X.value
  if ag.value then ⟨none,eq.work+X.work+ag.work+8⟩ else
   let u:=subtreeBits S f
   match u.value with
   | some (.leaf c)=>let z:=copyBits c;⟨some ⟨e,f,z.value⟩,eq.work+X.work+ag.work+u.work+z.work+12⟩
   | _=>⟨none,eq.work+X.work+ag.work+u.work+8⟩

@[simp] theorem badAtBits_value (T S : GenericForest.BinaryProvider.Tree) (e f : RMAF.Vertex) :
 (badAtBits T S e f).value.map badValue=Universal233.Rule5FinalClassification.badAt (treeValue T) (treeValue S) e f := by
 have sv:=subtreeBits_value S f
 simp only [badAtBits,meterAddressEq_value,restrictionAgreesStored_value,subtreeLeavesBits_value,sourceSubtreeLabels_eq]
 unfold Universal233.Rule5FinalClassification.badAt
 by_cases same : e=f
 · simp [same]
 · simp only [same,beq_iff_eq,if_false,true_and]
   cases ag : RMAF.restrictionAgrees (treeValue T) (treeValue S) (Universal233.HardParent.subtreeLabels (treeValue S) e)
   · simp only [Bool.false_eq_true,ite_false,ite_true]
     rw [←sv]
     cases h : (subtreeBits S f).value with
     | none=>simp [same,targetValue]
     | some U=>cases U <;> simp [same,targetValue,treeValue,badValue,labelValue]
   · simp

theorem badAtBits_provenance (T S : GenericForest.BinaryProvider.Tree) (e f : RMAF.Vertex) (d : BadBits)
 (h : (badAtBits T S e f).value=some d) : d.badArc=e ∧ d.singletonArc=f ∧ d.c∈leavesBits S := by
 dsimp only [badAtBits] at h
 split at h
 · contradiction
 · split at h
   · contradiction
   · cases u : (subtreeBits S f).value with
     | none=>simp [u] at h
     | some U=>
      cases U with
      | node l r=>simp [u] at h
      | leaf c=>
       simp only [u,copyBits_value,Option.some.injEq] at h;subst d
       exact ⟨rfl,rfl,subtreeBits_leaf_mem S (.leaf c) f u c (by simp [leavesBits])⟩

def badFor (T S : GenericForest.BinaryProvider.Tree) (e : RMAF.Vertex) : Addresses→Charged (List BadBits)
 | []=>⟨[],1⟩
 | f::fs=>let a:=badAtBits T S e f;let r:=badFor T S e fs
           ⟨match a.value with | none=>r.value | some d=>d::r.value,a.work+r.work+6⟩
@[simp] theorem badFor_value (T S : GenericForest.BinaryProvider.Tree) (e : RMAF.Vertex) (fs : Addresses) :
 (badFor T S e fs).value.map badValue=fs.filterMap (Universal233.Rule5FinalClassification.badAt (treeValue T) (treeValue S) e) := by
 induction fs with
 | nil=>rfl
 | cons f fs ih=>
  have a:=badAtBits_value T S e f
  simp only [badFor,List.filterMap_cons,←a]
  cases h : (badAtBits T S e f).value <;> simp [h,ih]

def badCandidatesFrom (T S : GenericForest.BinaryProvider.Tree) (fs : Addresses) : Addresses→Charged (List BadBits)
 | []=>⟨[],1⟩
 | e::es=>let a:=badFor T S e fs;let r:=badCandidatesFrom T S fs es;let c:=appendSpine a.value r.value
           ⟨c.value,a.work+r.work+c.work+8⟩
@[simp] theorem badCandidatesFrom_value (T S : GenericForest.BinaryProvider.Tree) (fs es : Addresses) :
 (badCandidatesFrom T S fs es).value.map badValue=es.flatMap (fun e=>fs.filterMap (Universal233.Rule5FinalClassification.badAt (treeValue T) (treeValue S) e)) := by
 induction es <;> simp_all [badCandidatesFrom]

def selectBadBits (T S : GenericForest.BinaryProvider.Tree) (a b : Bits) : Charged (Option BadBits):=
 let p:=pendantBits S a b;let c:=badCandidatesFrom T S p.value p.value
 ⟨c.value.head?,p.work+c.work+4⟩
@[simp] theorem selectBadBits_value (T S : GenericForest.BinaryProvider.Tree) (a b : Bits) :
 (selectBadBits T S a b).value.map badValue=Universal233.Rule5FinalClassification.selectBad (treeValue T) (treeValue S) (decode a) (decode b) := by
 simp only [selectBadBits,←List.head?_map,badCandidatesFrom_value,pendantBits_value,Universal233.Rule5FinalClassification.selectBad,Universal233.Rule5FinalClassification.badCandidates]

theorem badFor_provenance (T S : GenericForest.BinaryProvider.Tree) (e : RMAF.Vertex) (fs : Addresses) (d : BadBits)
 (h : d∈(badFor T S e fs).value) : d.badArc=e ∧ d.singletonArc∈fs ∧ d.c∈leavesBits S := by
 induction fs with
 | nil=>simp [badFor] at h
 | cons f fs ih=>
  cases a : (badAtBits T S e f).value with
  | none=>have r:=ih (by simpa only [badFor,a] using h);exact ⟨r.1,by simp [r.2.1],r.2.2⟩
  | some x=>
   simp only [badFor,a,List.mem_cons] at h
   rcases h with rfl|h
   · have r:=badAtBits_provenance T S e f d a;exact ⟨r.1,by simp [r.2.1],r.2.2⟩
   · have r:=ih h;exact ⟨r.1,by simp [r.2.1],r.2.2⟩

theorem badCandidatesFrom_provenance (T S : GenericForest.BinaryProvider.Tree) (fs es : Addresses) (d : BadBits)
 (h : d∈(badCandidatesFrom T S fs es).value) : d.badArc∈es ∧ d.singletonArc∈fs ∧ d.c∈leavesBits S := by
 induction es with
 | nil=>simp [badCandidatesFrom] at h
 | cons e es ih=>
  simp only [badCandidatesFrom,appendSpine_value,List.mem_append] at h
  rcases h with h|h
  · have r:=badFor_provenance T S e fs d h;exact ⟨by simp [r.1],r.2⟩
  · have r:=ih h;exact ⟨by simp [r.1],r.2⟩

theorem selectedBad_provenance (T S : GenericForest.BinaryProvider.Tree) (a b : Bits) (d : BadBits)
 (h : (selectBadBits T S a b).value=some d) :
 d.badArc∈(pendantBits S a b).value ∧ d.singletonArc∈(pendantBits S a b).value ∧ d.c∈leavesBits S := by
 exact badCandidatesFrom_provenance T S _ _ d (List.mem_of_head? h)
end OrdinaryDispatch.StoredNumeric.ClassifierReach
