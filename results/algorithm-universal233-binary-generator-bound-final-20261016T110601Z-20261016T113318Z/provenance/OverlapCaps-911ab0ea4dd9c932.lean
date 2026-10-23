import GeneratedBranchBounds
namespace GenericForest.BinaryProducer
open BinaryProvider Universal233.WholeSourceWork Universal233.CoreWork

theorem firstShared_mem (B A : Addresses) (v : RMAF.Vertex) (h : (firstShared B A).value=some v) : v∈A := by
 induction A with
 | nil=>simp [firstShared] at h
 | cons x xs ih=>
  dsimp only [firstShared] at h;split at h
  · cases h;simp
  · exact List.mem_cons_of_mem _ (ih h)

def OverlapCap (N I : Nat) (h : OverlapBits) : Prop := h.left.length≤I ∧ h.right.length≤I ∧ h.vertex.length≤N

theorem overlapRow_caps (N I : Nat) (t : BinaryProvider.Tree) (a : BinaryProvider.Tree×Bits) (bs : List (BinaryProvider.Tree×Bits))
 (tn : treeNodes (treeValue t)≤N) (ai : a.2.length≤I) (bi : ∀b∈bs,b.2.length≤I) :
 ∀h∈(overlapRow t a bs).value,OverlapCap N I h := by
 induction bs with
 | nil=>simp [overlapRow]
 | cons b bs ih=>
  have tail:=ih (fun x hx=>bi x (by simp [hx]))
  dsimp only [overlapRow];split
  · cases he : (firstShared (minimalLabels (leavesCopy b.1).value t).value (minimalLabels (leavesCopy a.1).value t).value).value with
    | none=>exact tail
    | some v=>
     intro h hh;rcases List.mem_cons.mp hh with rfl|hh
     · have vm:=firstShared_mem _ _ v he
       have vc:=(minimalLabels_caps N (leavesCopy a.1).value t tn).2 v vm
       exact ⟨ai,bi b (by simp),vc⟩
     · exact tail h hh
  · exact tail

theorem overlapRows_caps (N I : Nat) (t : BinaryProvider.Tree) (bs xs : List (BinaryProvider.Tree×Bits))
 (tn : treeNodes (treeValue t)≤N) (bi : ∀b∈bs,b.2.length≤I) (xi : ∀x∈xs,x.2.length≤I) :
 ∀h∈(overlapRows t bs xs).value,OverlapCap N I h := by
 induction xs with
 | nil=>simp [overlapRows]
 | cons a xs ih=>
  have row:=overlapRow_caps N I t a bs tn (xi a (by simp)) bi
  have tail:=ih (fun x hx=>xi x (by simp [hx]))
  simp only [overlapRows,appendSpine_value,List.mem_append]
  intro h hh;rcases hh with hh|hh
  · exact row h hh
  · exact tail h hh

theorem overlapProducer_caps (N S : Nat) (t : BinaryProvider.Tree) (ss : List BinaryProvider.Tree)
 (tn : treeNodes (treeValue t)≤N) (ssn : ss.length≤S) (h : OverlapBits) (he : (overlapProducer t ss).value=some h) :
 OverlapCap N S h := by
 have zi : ∀p∈(zipBits [] ss).value,p.2.length≤S:=by
  intro p hp;have z:=(zipBits_caps [] ss p hp).2;simp only [List.length_nil,Nat.zero_add] at z;omega
 have cap:=overlapRows_caps N S t _ _ tn zi zi
 have hm : h∈(overlapRows t (zipBits [] ss).value (zipBits [] ss).value).value:=by
  dsimp only [overlapProducer] at he
  cases ho : (overlapRows t (zipBits [] ss).value (zipBits [] ss).value).value with
  | nil=>simp only [ho,List.head?_nil] at he;contradiction
  | cons a rest=>simp only [ho,List.head?_cons,Option.some.injEq] at he;subst h;simp
 exact cap h hm
end GenericForest.BinaryProducer
