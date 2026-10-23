import StateForward
import Composition

namespace RestrictionBridge
open RMAF

theorem checked_flatten_perm (L : List Nat) (F : List (List Nat))
    (proper : L.Nodup) (hp : partitionCheck L F = true) : F.flatten.Perm L := by
  apply List.perm_iff_count.2
  intro x
  by_cases hx : x ∈ L
  · rw [checked_count L F hp hx,proper.count]
    simp [hx]
  · have hn : x ∉ F.flatten := by
      intro hm
      obtain ⟨B,hB,hxB⟩ := List.mem_flatten.1 hm
      exact hx (checked_label L F hp hB hxB)
    rw [List.count_eq_zero.2 hn,List.count_eq_zero.2 hx]

theorem checked_family_nodup (L : List Nat) (Q : List (List Nat))
    (hp : partitionCheck L Q = true) : Q.Nodup := by
  apply List.nodup_iff_count_of_mem.2
  intro U hU
  have hn := checked_nonempty L Q hp U hU
  obtain ⟨x,hx⟩ : ∃ x, x ∈ U := List.exists_mem_of_ne_nil U hn
  obtain ⟨V,hV,hxV,hcV,unique⟩ := unique_label_owner Q x
    (checked_count L Q hp (checked_label L Q hp hU hx))
  simpa [unique U hU hx] using hcV

theorem concat_flatten_perm (Q : List (List Nat)) (G : List Nat → List (List Nat))
    (hp : ∀ U ∈ Q, (G U).flatten.Perm U) :
    (Q.flatMap G).flatten.Perm Q.flatten := by
  induction Q with
  | nil => simp
  | cons U Q ih =>
    simp only [List.flatMap_cons,List.flatten_append,List.flatten_cons]
    exact (hp U (by simp)).append (ih (fun V hv => hp V (by simp [hv])))

theorem checked_concat (L : List Nat) (Q : List (List Nat)) (G : List Nat → List (List Nat))
    (hQ : partitionCheck L Q = true) (hlocal : ∀ U ∈ Q, partitionCheck U (G U) = true) :
    partitionCheck L (Q.flatMap G) = true := by
  have hp : (Q.flatMap G).flatten.Perm Q.flatten := concat_flatten_perm Q G (by
    intro U hU
    exact checked_flatten_perm U (G U) (checked_block_nodup L Q hQ U hU) (hlocal U hU))
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro B hB
    obtain ⟨U,hU,hB⟩ := List.mem_flatMap.1 hB
    have hn := checked_nonempty U (G U) (hlocal U hU) B hB
    simpa using hn
  · intro x hx
    apply beq_iff_eq.2
    rw [hp.count_eq x,checked_count L Q hQ hx]
  · intro x hx
    obtain ⟨U,hU,hxU⟩ := List.mem_flatten.1 (hp.mem_iff.1 hx)
    exact List.contains_iff_mem.2 (checked_label L Q hQ hU hxU)

theorem pairwise_iff (t : Tree) (F : List (List Nat)) :
    pairwiseEmbeddings t F = true ↔
      F.Pairwise (fun B C => Clear (minimalVertices B t) (minimalVertices C t)) := by
  induction F with
  | nil => simp [pairwiseEmbeddings]
  | cons B F ih => simp [pairwiseEmbeddings,List.pairwise_cons,List.all_eq_true,clear_iff,ih]

theorem pairwise_distinct (t : Tree) (Q : List (List Nat)) (hq : pairwiseEmbeddings t Q = true)
    (U V : List Nat) (hU : U ∈ Q) (hV : V ∈ Q) (hne : U ≠ V) :
    Clear (minimalVertices U t) (minimalVertices V t) := by
  induction Q with
  | nil => simp at hU
  | cons W Q ih =>
    simp only [pairwiseEmbeddings,Bool.and_eq_true,List.all_eq_true,clear_iff] at hq
    rcases List.mem_cons.1 hU with hu | hu <;> rcases List.mem_cons.1 hV with hv | hv
    · exact False.elim (hne (hu.trans hv.symm))
    · subst U; exact hq.1 V hv
    · subst V; exact (clear_symm _ _).1 (hq.1 U hu)
    · exact ih hq.2 hu hv

theorem cross_subblocks (t : Tree) (Q : List (List Nat))
    (hq : pairwiseEmbeddings t Q = true) (U V B C : List Nat)
    (hU : U ∈ Q) (hV : V ∈ Q) (hne : U ≠ V) (hBU : B ⊆ U) (hCV : C ⊆ V) :
    Clear (minimalVertices B t) (minimalVertices C t) := by
  intro v hB hC
  exact pairwise_distinct t Q hq U V hU hV hne v
    (VertexGeometry.executable_span_monotone t B U (fun _ hx => hBU hx) v hB)
    (VertexGeometry.executable_span_monotone t C V (fun _ hx => hCV hx) v hC)

theorem concat_pairwise (t : Tree) (Q : List (List Nat)) (G : List Nat → List (List Nat))
    (hn : Q.Nodup) (hq : pairwiseEmbeddings t Q = true)
    (hlocal : ∀ U ∈ Q, pairwiseEmbeddings t (G U) = true)
    (sub : ∀ U ∈ Q, ∀ B ∈ G U, B ⊆ U) : pairwiseEmbeddings t (Q.flatMap G) = true := by
  apply (pairwise_iff t _).2
  induction Q with
  | nil => simp
  | cons U Q ih =>
    have hnd := List.nodup_cons.1 hn
    have hqs : pairwiseEmbeddings t Q = true := by
      simp only [pairwiseEmbeddings,Bool.and_eq_true] at hq
      exact hq.2
    rw [List.flatMap_cons,List.pairwise_append]
    refine ⟨(pairwise_iff t (G U)).1 (hlocal U (by simp)),
      ih hnd.2 hqs (fun V hv => hlocal V (by simp [hv]))
        (fun V hv B hb => sub V (by simp [hv]) B hb),?_⟩
    intro B hb C hc
    obtain ⟨V,hV,hC⟩ := List.mem_flatMap.1 hc
    have hne : U ≠ V := by intro he; subst V; exact hnd.1 hV
    exact cross_subblocks t (U :: Q) hq U V B C (by simp) (by simp [hV]) hne
      (sub U (by simp) B hb) (sub V (by simp [hV]) C hC)

theorem local_checked_labels (T t : Tree) (U : List Nat) (Q : List (List Nat))
    (G : List (List Nat)) (proper : (leaves T).Nodup)
    (hQ : partitionCheck (leaves T) Q = true) (hU : U ∈ Q)
    (ht : restrict U T = some t) (hp : partitionCheck (leaves t) G = true) :
    partitionCheck U G = true := by
  have labels := component_labels T t U Q ht proper hQ hU
  exact (partition_labels_congr (leaves t) U G (fun x => labels.mem_iff)).1 hp

theorem checked_family_nonempty (L : List Nat) (G : List (List Nat))
    (hn : L ≠ []) (hp : partitionCheck L G = true) : G ≠ [] := by
  obtain ⟨x,hx⟩ : ∃ x, x ∈ L := List.exists_mem_of_ne_nil L hn
  obtain ⟨B,hB,hxB⟩ := checked_covers L G hp hx
  intro he; rw [he] at hB; simp at hB

/-- The indexed data are ordinary trees and block lists. The hypotheses contain
only literal restrictions, local checker results, and original checked Q data;
no embedding transport, reconstruction, or budget conclusion is supplied. -/
theorem reverse_reconstruction (T S : Tree) (Q : List (List Nat))
    (G : List Nat → List (List Nat)) (t s : List Nat → Tree)
    (properT : (leaves T).Nodup) (properS : (leaves S).Nodup)
    (hQT : partitionCheck (leaves T) Q = true)
    (hQS : partitionCheck (leaves S) Q = true)
    (eT : pairwiseEmbeddings T Q = true) (eS : pairwiseEmbeddings S Q = true)
    (ht : ∀ U ∈ Q, restrict U T = some (t U))
    (hs : ∀ U ∈ Q, restrict U S = some (s U))
    (ha : ∀ U ∈ Q, agreement (t U) (s U) (G U) = true) :
    agreement T S (Q.flatMap G) = true ∧
    (Q.map (fun U => (G U).length - 1)).sum = (Q.flatMap G).length - Q.length ∧
    (Q.flatMap G).flatten.Perm (leaves T) ∧ (Q.flatMap G).flatten.Perm (leaves S) := by
  have hp : ∀ U ∈ Q, partitionCheck U (G U) = true := by
    intro U hU
    have hh := ha U hU
    simp only [agreement,Bool.and_eq_true] at hh
    exact local_checked_labels T (t U) U Q (G U) properT hQT hU (ht U hU) hh.1.1.1.1
  have hsub : ∀ U ∈ Q, ∀ B ∈ G U, B ⊆ U := by
    intro U hU B hB x hx
    exact checked_label U (G U) (hp U hU) hB hx
  have pT : partitionCheck (leaves T) (Q.flatMap G) = true := checked_concat (leaves T) Q G hQT hp
  have pS : partitionCheck (leaves S) (Q.flatMap G) = true := checked_concat (leaves S) Q G hQS hp
  have origT : ∀ U ∈ Q, pairwiseEmbeddings T (G U) = true := by
    intro U hU
    have hh := ha U hU
    simp only [agreement,Bool.and_eq_true] at hh
    exact (pairwise_transport T (t U) U (G U) (ht U hU) (hsub U hU)).2 hh.1.2
  have origS : ∀ U ∈ Q, pairwiseEmbeddings S (G U) = true := by
    intro U hU
    have hh := ha U hU
    simp only [agreement,Bool.and_eq_true] at hh
    exact (pairwise_transport S (s U) U (G U) (hs U hU) (hsub U hU)).2 hh.2
  have hagree : agreement T S (Q.flatMap G) = true := by
    simp only [agreement,Bool.and_eq_true]
    refine ⟨⟨⟨⟨pT,pS⟩,?_⟩,
      concat_pairwise T Q G (checked_family_nodup (leaves T) Q hQT) eT origT hsub⟩,
      concat_pairwise S Q G (checked_family_nodup (leaves S) Q hQS) eS origS hsub⟩
    apply List.all_eq_true.2
    intro B hB
    obtain ⟨U,hU,hB⟩ := List.mem_flatMap.1 hB
    have hh := ha U hU
    simp only [agreement,Bool.and_eq_true] at hh
    rw [←sameShape_restrict_inside T S (t U) (s U) U B (ht U hU) (hs U hU) (hsub U hU B hB)]
    exact List.all_eq_true.1 hh.1.1.2 B hB
  refine ⟨hagree,?_,checked_flatten_perm (leaves T) (Q.flatMap G) properT pT,
    checked_flatten_perm (leaves S) (Q.flatMap G) properS pS⟩
  have pos : ∀ U ∈ Q, 0 < (G U).length := by
    intro U hU
    exact List.length_pos_iff.2 (checked_family_nonempty U (G U)
      (checked_nonempty (leaves T) Q hQT U hU) (hp U hU))
  have hb := sum_sub_one Q (fun U => (G U).length) pos
  rw [List.length_flatMap]
  omega

end RestrictionBridge
