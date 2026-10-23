import Marked
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

def clipBlock (X B : List Nat) : Option (List Nat) :=
  let D := B.filter (X.contains ·)
  if D.isEmpty then none else some D
def clip (X : List Nat) (F : List (List Nat)) := F.filterMap (clipBlock X)

theorem clipBlock_some (X B D : List Nat) (h : clipBlock X B=some D) :
    D=B.filter (X.contains ·) ∧ D≠[] := by
  unfold clipBlock at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i hn
    have he : B.filter (X.contains ·)=D := Option.some.inj h
    exact ⟨he.symm,by intro hD;rw [he,hD] at hn;simp at hn⟩

theorem clip_mem (X : List Nat) (F : List (List Nat)) (D : List Nat) (h : D∈clip X F) :
    ∃ B∈F, D=B.filter (X.contains ·) ∧ D≠[] := by
  obtain ⟨B,hB,hBD⟩ := List.mem_filterMap.1 h
  exact ⟨B,hB,(clipBlock_some X B D hBD).1,(clipBlock_some X B D hBD).2⟩

theorem clip_sub (X : List Nat) (F : List (List Nat)) : ∀ D∈clip X F, D⊆X := by
  intro D hD
  obtain ⟨B,hB,rfl,hne⟩ := clip_mem X F D hD
  intro x hx
  exact List.contains_iff_mem.1 (List.mem_filter.1 hx).2

theorem clip_length (X : List Nat) (F : List (List Nat)) : (clip X F).length≤F.length :=
  List.length_filterMap_le _ _

theorem clip_flatten (X : List Nat) (F : List (List Nat)) :
    (clip X F).flatten=F.flatten.filter (X.contains ·) := by
  induction F with
  | nil => rfl
  | cons B F ih =>
    have hc : clip X (B::F) =
        if (B.filter (X.contains ·)).isEmpty then clip X F
        else (B.filter (X.contains ·))::clip X F := by
      by_cases h : (B.filter (X.contains ·)).isEmpty=true
      · simp only [clip,List.filterMap_cons,clipBlock,h,ite_true]
      · simp only [clip,List.filterMap_cons,clipBlock,h,Bool.false_eq_true,ite_false]
    rw [hc]
    cases he : (B.filter (X.contains ·)).isEmpty with
    | true =>
      have hb : B.filter (X.contains ·)=[] := List.isEmpty_iff.1 he
      simp only [ite_true,List.flatten_cons,List.filter_append,hb,List.nil_append,ih]
    | false =>
      simp only [Bool.false_eq_true,ite_false,List.flatten_cons,List.filter_append,ih]

theorem clip_partition (t u : Tree) (X : List Nat) (F : List (List Nat))
    (hu : restrict X t=some u) (hp : partitionCheck (leaves t) F=true) :
    partitionCheck (leaves u) (clip X F)=true := by
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro D hD
    have ne := (clip_mem X F D hD).choose_spec.2.2
    cases D <;> simp_all
  · intro x hx
    obtain ⟨hxt,hxX⟩ := (restricted_labels_exact t u X hu).1 hx
    rw [clip_flatten,List.count_filter (List.contains_iff_mem.2 hxX),checked_count _ F hp hxt]
    rfl
  · intro x hx
    rw [clip_flatten] at hx
    obtain ⟨hxF,hxX⟩ := List.mem_filter.1 hx
    apply List.contains_iff_mem.2
    exact (restricted_labels_exact t u X hu).2
      ⟨Universal233.SourceCoverage.partitionCheck_subset (leaves t) F hp hxF,List.contains_iff_mem.1 hxX⟩

theorem clip_embeddings (t : Tree) (X : List Nat) (F : List (List Nat))
    (he : pairwiseEmbeddings t F=true) : pairwiseEmbeddings t (clip X F)=true := by
  apply (pairwise_iff t (clip X F)).2
  apply List.Pairwise.filterMap (clipBlock X) ?_ ((pairwise_iff t F).1 he)
  intro B C hclear D hD E hE
  obtain ⟨rfl,hnD⟩ := clipBlock_some X B D hD
  obtain ⟨rfl,hnE⟩ := clipBlock_some X C E hE
  intro v hvB hvC
  exact hclear v
    (VertexGeometry.executable_span_monotone t _ B (fun x hx => (List.mem_filter.1 hx).1) v hvB)
    (VertexGeometry.executable_span_monotone t _ C (fun x hx => (List.mem_filter.1 hx).1) v hvC)

/-- Ordinary restriction/deletion never increases the number of final blocks.
All topology and original embedding checks are transported, not just values. -/
theorem agreement_clip (T S t s : Tree) (X : List Nat) (F : List (List Nat))
    (ht : restrict X T=some t) (hs : restrict X S=some s) (ha : agreement T S F=true) :
    agreement t s (clip X F)=true ∧ (clip X F).length≤F.length := by
  have hh:=ha
  simp only [agreement,Bool.and_eq_true] at hh
  refine ⟨?_,clip_length X F⟩
  simp only [agreement,Bool.and_eq_true]
  refine ⟨⟨⟨⟨clip_partition T t X F ht hh.1.1.1.1,clip_partition S s X F hs hh.1.1.1.2⟩,?_⟩,?_⟩,?_⟩
  · apply List.all_eq_true.2
    intro D hD
    obtain ⟨B,hB,hBD,hne⟩ := clip_mem X F D hD
    have Dsub : D⊆B := by
      rw [hBD]
      intro x hx
      exact (List.mem_filter.1 hx).1
    have Dlab : D⊆leaves T := fun x hx => checked_label _ F hh.1.1.1.1 hB (Dsub hx)
    obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil D hne
    have top := BinaryExchange.restrictionAgrees_sub T S B D
      (List.all_eq_true.1 hh.1.1.2 B hB) (fun _ hx => Dsub hx) ⟨x,hx,Dlab hx⟩
    rw [sameShape_restrict_inside T S t s X D ht hs (clip_sub X F D hD)]
    exact top
  · exact (pairwise_transport T t X (clip X F) ht (clip_sub X F)).1 (clip_embeddings T X F hh.1.2)
  · exact (pairwise_transport S s X (clip X F) hs (clip_sub X F)).1 (clip_embeddings S X F hh.2)
end OrdinaryCommonSplit
