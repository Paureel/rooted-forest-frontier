import ProducerCostSchedulerLedger
namespace GenericForest.BinaryProducer
open BinaryProvider GenericForest.ScalarBits GenericForest.CheckCorrespondence Universal233.WholeSourceWork
structure OverlapBits where
 left : Bits
 right : Bits
 vertex : RMAF.Vertex
 deriving Repr
def overlapValue (h : OverlapBits) : GenericForest.Overlap:=⟨decode h.left,decode h.right,h.vertex⟩
def indexedValue (p : BinaryProvider.Tree×Bits) : RMAF.Tree×Nat:=(treeValue p.1,decode p.2)
def zipBits (i : Bits) : List BinaryProvider.Tree→Charged (List (BinaryProvider.Tree×Bits))
 | []=>⟨[],1⟩
 | s::ss=>let n:=incrementBits i;let r:=zipBits n.value ss;⟨(s,i)::r.value,n.work+r.work+8⟩
@[simp] theorem zipBits_value (i : Bits) (ss : List BinaryProvider.Tree) :
 (zipBits i ss).value.map indexedValue=(sourcesValue ss).zipIdx (decode i) := by
 induction ss generalizing i with
 | nil=>rfl
 | cons s ss ih=>simp [zipBits,indexedValue,List.zipIdx_cons,sourcesValue,ih]

theorem minimalLabels_value (B : Block) (T : BinaryProvider.Tree) :
 (minimalLabels B T).value=RMAF.minimalVertices (blockValue B) (treeValue T) := by
 let C:=(prepareCapacity B [leavesBits T]).value
 have r:=prepareCapacity_spec B [leavesBits T]
 exact (minimalLabels_projects C.length B T r.1 (r.2.1 (leavesBits T) (by simp))).1.trans (meterMinimal_value _ _)

def firstShared (B : Addresses) : Addresses→Charged (Option RMAF.Vertex)
 | []=>⟨none,1⟩
 | v::vs=>let c:=meterVertexContains v B
           if c.value then ⟨some v,c.work+4⟩ else let r:=firstShared B vs;⟨r.value,c.work+r.work+4⟩
@[simp] theorem firstShared_value (A B : Addresses) :
 (firstShared B A).value=A.find? (fun v=>B.contains v) := by
 induction A with
 | nil=>rfl
 | cons v vs ih=>simp [firstShared,meterVertexContains_value,List.find?_cons,ih];split <;> simp_all

def indexLt (a b : Bits) : Charged Bool:=let n:=incrementBits a;let l:=leBits n.value b;⟨l.value,n.work+l.work+4⟩
@[simp] theorem indexLt_value (a b : Bits) : (indexLt a b).value=decide (decode a<decode b) := by
 simp only [indexLt,leBits_value,incrementBits_value]
 congr 1 <;> omega

def overlapRow (t : BinaryProvider.Tree) (a : BinaryProvider.Tree×Bits) : List (BinaryProvider.Tree×Bits)→Charged (List OverlapBits)
 | []=>⟨[],1⟩
 | b::bs=>let lt:=indexLt a.2 b.2;let r:=overlapRow t a bs
  if lt.value then
   let al:=leavesCopy a.1;let bl:=leavesCopy b.1
   let ah:=minimalLabels al.value t;let bh:=minimalLabels bl.value t;let c:=firstShared bh.value ah.value
   ⟨match c.value with | none=>r.value | some v=>⟨a.2,b.2,v⟩::r.value,
    lt.work+r.work+al.work+bl.work+ah.work+bh.work+c.work+12⟩
  else ⟨r.value,lt.work+r.work+4⟩

def overlapRows (t : BinaryProvider.Tree) (bs : List (BinaryProvider.Tree×Bits)) : List (BinaryProvider.Tree×Bits)→Charged (List OverlapBits)
 | []=>⟨[],1⟩
 | a::as=>let row:=overlapRow t a bs;let r:=overlapRows t bs as;let ap:=appendSpine row.value r.value
           ⟨ap.value,row.work+r.work+ap.work+8⟩

theorem overlapRow_value (t : BinaryProvider.Tree) (a : BinaryProvider.Tree×Bits) (bs : List (BinaryProvider.Tree×Bits)) :
 (overlapRow t a bs).value.map overlapValue=(bs.map indexedValue).filterMap (fun b=>
 if decode a.2<b.2 then
  ((RMAF.minimalVertices (RMAF.leaves (treeValue a.1)) (treeValue t)).find? (fun v=>
   (RMAF.minimalVertices (RMAF.leaves b.1) (treeValue t)).contains v)).map (GenericForest.Overlap.mk (decode a.2) b.2)
 else none) := by
 induction bs with
 | nil=>rfl
 | cons b bs ih=>
  simp only [overlapRow,indexLt_value,List.map_cons,List.filterMap_cons,indexedValue]
  split
  · simp only [leavesCopy_value,minimalLabels_value,leaves_projection,firstShared_value]
    cases h : (RMAF.minimalVertices (RMAF.leaves (treeValue a.1)) (treeValue t)).find? (fun v=>
     (RMAF.minimalVertices (RMAF.leaves (treeValue b.1)) (treeValue t)).contains v) <;> simp_all [overlapValue]
  · rename_i h
    have no : ¬decode a.2<decode b.2:=by simpa only [decide_eq_true_eq] using h
    simp only [no,ite_false,ih]

theorem overlapRows_value (t : BinaryProvider.Tree) (bs xs : List (BinaryProvider.Tree×Bits)) :
 (overlapRows t bs xs).value.map overlapValue=(xs.map indexedValue).flatMap (fun a=>
  (bs.map indexedValue).filterMap (fun b=>if a.2<b.2 then
   ((RMAF.minimalVertices (RMAF.leaves a.1) (treeValue t)).find? (fun v=>
    (RMAF.minimalVertices (RMAF.leaves b.1) (treeValue t)).contains v)).map (GenericForest.Overlap.mk a.2 b.2)
   else none)) := by
 induction xs with
 | nil=>rfl
 | cons a xs ih=>simp [overlapRows,overlapRow_value,ih,indexedValue,List.map_append]

def overlapProducer (t : BinaryProvider.Tree) (ss : List BinaryProvider.Tree) : Charged (Option OverlapBits):=
 let z:=zipBits [] ss;let r:=overlapRows t z.value z.value;⟨r.value.head?,z.work+r.work+4⟩
theorem overlapProducer_value (t : BinaryProvider.Tree) (ss : List BinaryProvider.Tree) :
 (overlapProducer t ss).value.map overlapValue=GenericForest.overlap (treeValue t) (sourcesValue ss) := by
 have r:=overlapRows_value t (zipBits [] ss).value (zipBits [] ss).value
 simp only [zipBits_value,decode] at r
 simp only [overlapProducer,GenericForest.overlap]
 rw [←r]
 cases (overlapRows t (zipBits [] ss).value (zipBits [] ss).value).value <;> rfl
end GenericForest.BinaryProducer
