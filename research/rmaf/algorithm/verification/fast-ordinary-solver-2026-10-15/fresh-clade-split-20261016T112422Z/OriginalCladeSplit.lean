import PartitionRefine
namespace FreshClade
open RMAF Universal233.CoreGraph Universal233

def HullDisjoint (T : Tree) (B C : List Nat) : Prop :=
 disjointVertices (minimalVertices B T) (minimalVertices C T)=true

theorem embeddings_pairwise (T : Tree) (F : List (List Nat)) :
 pairwiseEmbeddings T F=true ↔ F.Pairwise (HullDisjoint T) := by
 induction F with
 | nil => simp [pairwiseEmbeddings]
 | cons B F ih => simp [pairwiseEmbeddings,List.pairwise_cons,List.all_eq_true,ih,HullDisjoint]

theorem splitBlock_pairwise (X B : List Nat) (T : Tree)
 (h : HullDisjoint T (B.filter X.contains) (B.filter (fun x=> !X.contains x))) :
 (splitBlock X B).Pairwise (HullDisjoint T) := by
 have raw : [B.filter X.contains,B.filter (fun x=> !X.contains x)].Pairwise (HullDisjoint T) := by
  simpa using h
 exact raw.filter (fun B=> !B.isEmpty)

theorem embeddings_refine (X : List Nat) (T : Tree) (F : List (List Nat))
 (h : pairwiseEmbeddings T F=true)
 (self : ∀B, B∈F → HullDisjoint T (B.filter X.contains) (B.filter (fun x=> !X.contains x))) :
 pairwiseEmbeddings T (splitForest X F)=true := by
 rw [embeddings_pairwise] at h ⊢
 induction F with
 | nil => simp [splitForest]
 | cons B F ih =>
   simp only [List.pairwise_cons] at h
   have hp := splitBlock_pairwise X B T (self B (by simp))
   have ht := ih h.2 (fun C hC => self C (by simp [hC]))
   change (splitBlock X B ++ splitForest X F).Pairwise (HullDisjoint T)
   rw [List.pairwise_append]
   refine ⟨hp,ht,?_⟩
   intro C hC D hD
   rcases splitForest_origin hD with ⟨E,hE,hDE⟩
   exact disjoint_mono (splitBlock_subset hC) (splitBlock_subset hDE) (h.1 E hE)

theorem original_clade_split_agreement {T S U : Tree} {p : Vertex} {F : List (List Nat)}
 (proper : DepthOne.proper T S=true) (source : subtree S p=some U)
 (a : agreement T S F=true) : agreement T S (splitForest (leaves U) F)=true := by
 have unique : (leaves S).Nodup := by
  simp only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq] at proper
  exact proper.1.2
 simp only [agreement,Bool.and_eq_true,List.all_eq_true] at a ⊢
 rcases a with ⟨⟨⟨⟨pT,pS⟩,shapes⟩,hT⟩,hS⟩
 refine ⟨⟨⟨⟨partition_refine _ _ _ pT,partition_refine _ _ _ pS⟩,?_⟩,?_⟩,?_⟩
 · intro C hC
   rcases splitForest_origin hC with ⟨B,hB,hCB⟩
   exact restriction_refine B C (splitBlock_subset hCB) (splitBlock_nonempty hCB)
    (fun x hx => partition_labels pT hB x (splitBlock_subset hCB x hx)) (shapes B hB)
 · exact embeddings_refine (leaves U) T F hT (fun B hB =>
    (clade_split_hulls B unique source (shapes B hB)).1)
 · exact embeddings_refine (leaves U) S F hS (fun B hB =>
    (clade_split_hulls B unique source (shapes B hB)).2)

#print axioms original_clade_split_agreement
end FreshClade
