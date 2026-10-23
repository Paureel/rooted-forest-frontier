import ProducerBudgetTrim
import StoredSourceSite
import ProducerCostPretest
namespace OrdinaryDispatch.StoredNumeric.ProducerBinding
open RMAF GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer
open Universal233.WholeSourceWork Universal233.CoreWork GenericForest.CheckCorrespondence

def parentCopy : RMAF.Vertex → Charged RMAF.Vertex
 | []=>⟨[],1⟩
 | [_]=>⟨[],4⟩
 | a::b::bs=>let r:=parentCopy (b::bs);⟨a::r.value,r.work+4⟩
@[simp] theorem parentCopy_value (p : RMAF.Vertex) : (parentCopy p).value=p.dropLast := by
 induction p with
 | nil=>rfl
 | cons a ps ih=>cases ps <;> simp_all [parentCopy,List.dropLast]
theorem parentCopy_work (p : RMAF.Vertex) : (parentCopy p).work≤4*(p.length+1) := by
 induction p with
 | nil=>simp [parentCopy]
 | cons a ps ih=>cases ps <;> simp only [parentCopy,List.length_cons,List.length_nil] at * <;> omega

def pendantFilter (H : Addresses) : Addresses → Charged Addresses
 | []=>⟨[],1⟩
 | p::ps=>let d:=parentCopy p;let a:=meterVertexContains d.value H;let b:=meterVertexContains p H
           let r:=pendantFilter H ps
           ⟨if !p.isEmpty && a.value && !b.value then p::r.value else r.value,d.work+a.work+b.work+r.work+12⟩
@[simp] theorem pendantFilter_value (H V : Addresses) :
 (pendantFilter H V).value=V.filter (fun p=>!p.isEmpty && H.contains p.dropLast && !H.contains p) := by
 induction V <;> simp_all [pendantFilter,List.filter_cons]
theorem pendantFilter_sublist (H V : Addresses) : (pendantFilter H V).value.Sublist V := by
 rw [pendantFilter_value];exact List.filter_sublist

def pendantBits (S : GenericForest.BinaryProvider.Tree) (a b : Bits) : Charged Addresses :=
 let v:=verticesBits S;let h:=minimalLabels [a,b] S;let f:=pendantFilter h.value v.value
 ⟨f.value,v.work+h.work+f.work+12⟩
@[simp] theorem pendantBits_value (S : GenericForest.BinaryProvider.Tree) (a b : Bits) :
 (pendantBits S a b).value=Universal233.CherryBranching.cuts (treeValue S) (decode a) (decode b) := by
 simp only [pendantBits,pendantFilter_value,verticesBits_value,minimalLabels_value,blockValue,List.map_cons,List.map_nil,labelValue]
 rw [Universal233.Rule5CommonSelector.vertices_exact]
 rfl

theorem sourceSubtreeLabels_eq (S : RMAF.Tree) (p : RMAF.Vertex) :
 Universal233.DepthOne.subtreeLabels S p=Universal233.HardParent.subtreeLabels S p := by
 induction p generalizing S with
 | nil=>rfl
 | cons b ps ih=>cases S <;> cases b <;> simp_all [Universal233.DepthOne.subtreeLabels,Universal233.HardParent.subtreeLabels,Universal233.CoreGraph.subtree]

def subtreeUnion (S : GenericForest.BinaryProvider.Tree) : Addresses → Charged Block
 | []=>⟨[],1⟩
 | p::ps=>let l:=subtreeLeavesBits S p;let r:=subtreeUnion S ps;let a:=appendLabels l.value r.value
           ⟨a.value,l.work+r.work+a.work+8⟩
@[simp] theorem subtreeUnion_value (S : GenericForest.BinaryProvider.Tree) (ps : Addresses) :
 blockValue (subtreeUnion S ps).value=(ps.map (Universal233.HardParent.subtreeLabels (treeValue S))).flatten := by
 induction ps with
 | nil=>rfl
 | cons p ps ih=>simp only [subtreeUnion,appendLabels_value,blockValue_append,subtreeLeavesBits_value,sourceSubtreeLabels_eq,ih,List.map_cons,List.flatten_cons]

def coreSelectorBits (S : GenericForest.BinaryProvider.Tree) (a b : Bits) : Charged Block :=
 let p:=pendantBits S a b;let u:=subtreeUnion S p.value;let l:=leavesCopy S
 let e:=excludeLabels u.value l.value
 ⟨e.value,p.work+u.work+l.work+e.work+16⟩
@[simp] theorem coreSelectorBits_value (S : GenericForest.BinaryProvider.Tree) (a b : Bits) :
 blockValue (coreSelectorBits S a b).value=Universal233.CherryBranching.coreLabels (treeValue S) (decode a) (decode b) := by
 simp [coreSelectorBits,excludeLabels_value,subtreeUnion_value,pendantBits_value,leaves_projection,Universal233.CherryBranching.coreLabels]

def outsideSelectorBits (S : GenericForest.BinaryProvider.Tree) (a b c : Bits) : Charged Block :=
 let k:=coreSelectorBits S a b;let z:=copyBits c;let y:=appendLabels k.value [z.value]
 ⟨y.value,k.work+z.work+y.work+8⟩
@[simp] theorem outsideSelectorBits_value (S : GenericForest.BinaryProvider.Tree) (a b c : Bits) :
 blockValue (outsideSelectorBits S a b c).value=Universal233.CherryBranching.coreLabels (treeValue S) (decode a) (decode b)++[decode c] := by
 simp only [outsideSelectorBits,appendLabels_value,blockValue_append,copyBits_value,coreSelectorBits_value];rfl

/-- Copies the actual first stored representative. Empty selectors use empty
zero exactly as source headD 0, including before guards refuse them. -/
def headRepresentative : Block → Charged Bits
 | []=>⟨[],4⟩
 | x::_=>let c:=copyBits x;⟨c.value,c.work+4⟩
@[simp] theorem headRepresentative_value (X : Block) :
 decode (headRepresentative X).value=(blockValue X).headD 0 := by
 cases X <;> simp [headRepresentative,blockValue,labelValue,decode]
theorem headRepresentative_width (B : Nat) (X : Block) (cap : BlockWidth B X) :
 (headRepresentative X).value.length≤B := by
 cases X with
 | nil=>simp [headRepresentative]
 | cons x xs=>have h:=cap x (by simp);change x.length≤B at h;simpa [headRepresentative] using h
theorem headRepresentative_work (B : Nat) (X : Block) (cap : BlockWidth B X) :
 (headRepresentative X).work≤4*B+5 := by
 cases X with
 | nil=>simp [headRepresentative]
 | cons x xs=>have h:=cap x (by simp);change x.length≤B at h;simp [headRepresentative,copyBits_work];omega

theorem coreSelectorBits_width (B : Nat) (S : GenericForest.BinaryProvider.Tree) (a b : Bits) (cap : TreeWidth B S) :
 BlockWidth B (coreSelectorBits S a b).value := by
 intro x hx
 exact cap x (excludeLabels_mem _ _ x (by simpa only [coreSelectorBits,leavesCopy_value] using hx))
theorem coreSelectorBits_length (S : GenericForest.BinaryProvider.Tree) (a b : Bits) :
 (coreSelectorBits S a b).value.length≤(leavesBits S).length := by
 simpa only [coreSelectorBits,leavesCopy_value] using excludeLabels_count (subtreeUnion S (pendantBits S a b).value).value (leavesBits S)
theorem outsideSelectorBits_width (B : Nat) (S : GenericForest.BinaryProvider.Tree) (a b c : Bits)
 (cap : TreeWidth B S) (cc : c.length≤B) : BlockWidth B (outsideSelectorBits S a b c).value := by
 intro x hx
 simp only [outsideSelectorBits,appendLabels_value,copyBits_value,List.mem_append,List.mem_singleton] at hx
 rcases hx with hx|rfl
 · exact coreSelectorBits_width B S a b cap x hx
 · exact cc
end OrdinaryDispatch.StoredNumeric.ProducerBinding
