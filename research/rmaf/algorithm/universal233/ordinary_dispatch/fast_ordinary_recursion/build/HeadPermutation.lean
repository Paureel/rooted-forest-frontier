import OriginalGlue
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

/-- Local specialization of the completed final-recovery permutation method;
that completed proof was a declared development contact, not an independent
check of this arm. Original list order remains in every consumer. -/
theorem partition_cons_perm (labels H K : List Nat) (F : List (List Nat)) (h : H.Perm K) :
    partitionCheck labels (H::F)=partitionCheck labels (K::F) := by
  have flat : (H::F).flatten.Perm (K::F).flatten := by
    simpa only [List.flatten_cons] using h.append_right F.flatten
  have empty : H.isEmpty=K.isEmpty := h.isEmpty_eq
  have ct : (fun x => (H::F).flatten.count x==1)=(fun x => (K::F).flatten.count x==1) := by
    funext x
    rw [flat.count_eq x]
  simp only [partitionCheck,List.all_cons,empty,ct,flat.all_eq]

theorem embeddings_cons_perm (t : Tree) (H K : List Nat) (F : List (List Nat)) (h : H.Perm K) :
    pairwiseEmbeddings t (H::F)=pairwiseEmbeddings t (K::F) := by
  simp only [pairwiseEmbeddings,Universal233.DepthOne.minimal_members t H K (fun _ => h.mem_iff)]

theorem agreement_cons_perm (T S : Tree) (H K : List Nat) (F : List (List Nat)) (h : H.Perm K) :
    agreement T S (H::F)=agreement T S (K::F) := by
  have hrT := Universal233.DepthOne.restrict_members T H K (fun _ => h.mem_iff)
  have hrS := Universal233.DepthOne.restrict_members S H K (fun _ => h.mem_iff)
  simp only [agreement,partition_cons_perm _ H K F h,List.all_cons,restrictionAgrees,
    hrT,hrS,embeddings_cons_perm _ H K F h]

theorem embeddings_outer_perm (t : Tree) (F G : List (List Nat)) (h : F.Perm G)
    (he : pairwiseEmbeddings t F=true) : pairwiseEmbeddings t G=true := by
  apply (pairwise_iff t G).2
  exact (h.pairwise_iff (by intro B C hc;exact (clear_symm _ _).1 hc)).1 ((pairwise_iff t F).1 he)
end OrdinaryCommonSplit
