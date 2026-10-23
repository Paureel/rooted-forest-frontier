import GeneratorBoundControls
namespace GenericForest.BinaryProducer.OrdinaryBits
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork Universal233.CoreWork

def dropLastBits : RMAF.Vertex→Charged RMAF.Vertex
 | []=>⟨[],1⟩ | [_]=>⟨[],4⟩
 | x::y::xs=>let r:=dropLastBits (y::xs);⟨x::r.value,r.work+4⟩
@[simp] theorem dropLastBits_value (p : RMAF.Vertex) : (dropLastBits p).value=p.dropLast := by
 induction p with
 | nil=>rfl
 | cons x xs ih=>cases xs <;> simp_all [dropLastBits,List.dropLast]
theorem dropLastBits_cost (p : RMAF.Vertex) : (dropLastBits p).work≤4*p.length+1 := by
 induction p with
 | nil=>decide
 | cons x xs ih=>cases xs <;> simp_all only [dropLastBits,List.length_cons,List.length_nil] <;> omega

def cutFilter (span : Addresses) : Addresses→Charged Addresses
 | []=>⟨[],1⟩
 | p::ps=>let r:=cutFilter span ps
  if p.isEmpty then ⟨r.value,r.work+4⟩ else
   let d:=dropLastBits p;let parent:=meterVertexContains d.value span
   if parent.value then let inside:=meterVertexContains p span
                        ⟨if inside.value then r.value else p::r.value,r.work+d.work+parent.work+inside.work+12⟩
   else ⟨r.value,r.work+d.work+parent.work+8⟩
@[simp] theorem cutFilter_value (span ps : Addresses) :
 (cutFilter span ps).value=ps.filter (fun p=>!p.isEmpty && span.contains p.dropLast && !(span.contains p)) := by
 induction ps with
 | nil=>rfl
 | cons p ps ih=>
  simp only [cutFilter,List.filter_cons,dropLastBits_value,meterVertexContains_value]
  cases e : p.isEmpty <;> simp only [e,Bool.not_false,Bool.not_true,Bool.false_and,Bool.true_and,Bool.false_eq_true,ite_false,ite_true]
  · cases h : span.contains p.dropLast <;> cases h' : span.contains p <;> simp_all only [Bool.false_and,Bool.true_and,Bool.false_eq_true,Bool.not_false,Bool.not_true,ite_false,ite_true]
  · exact ih

def cutsBits (S : BinaryProvider.Tree) (a b : Bits) : Charged Addresses:=
 let v:=verticesBits S;let span:=minimalLabels [a,b] S;let r:=cutFilter span.value v.value
 ⟨r.value,v.work+span.work+r.work+8⟩

theorem vertices_original (S : BinaryProvider.Tree) : (verticesBits S).value=Universal233.HardParent.vertices (treeValue S) := by
 induction S <;> simp_all [verticesBits,joinAddresses_value,treeValue,Universal233.HardParent.vertices,RMAF.prependSide]

theorem cutsBits_value (S : BinaryProvider.Tree) (a b : Bits) :
 (cutsBits S a b).value=Universal233.CherryBranching.cuts (treeValue S) (decode a) (decode b) := by
 simp only [cutsBits,cutFilter_value,minimalLabels_value,vertices_original,blockValue,List.map_cons,List.map_nil,labelValue]
 rfl

theorem cutFilter_mem (span ps : Addresses) : ∀p∈(cutFilter span ps).value,p∈ps := by
 rw [cutFilter_value];exact fun p hp=>(List.mem_filter.mp hp).1

theorem cutsBits_caps (N : Nat) (S : BinaryProvider.Tree) (a b : Bits) (sn : treeNodes (treeValue S)≤N) :
 (cutsBits S a b).value.length≤N ∧ ∀p∈(cutsBits S a b).value,p.length≤N := by
 have count : (cutFilter (minimalLabels [a,b] S).value (verticesBits S).value).value.length≤(verticesBits S).value.length:=by
  rw [cutFilter_value];exact List.length_filter_le _ _
 refine ⟨by simp only [cutsBits];rw [verticesBits_count] at count;omega,?_⟩
 intro p hp
 have m:=cutFilter_mem _ (verticesBits S).value p hp
 exact Nat.le_trans (verticesBits_paths S p m) sn
end GenericForest.BinaryProducer.OrdinaryBits
