import Pretest
import ValidPartition
import Partition

namespace Universal233.DepthOne
open RMAF CoreGraph CutRealization RestrictionBridge Integration

theorem mem_vertices (S : Tree) (p : Vertex) : p ∈ vertices S ↔ Valid S p := by
  induction S generalizing p with
  | leaf x => cases p <;> simp [vertices,Valid,subtree]
  | node l r hl hr =>
    cases p with
    | nil => simp [vertices,Valid,subtree]
    | cons b p =>
      cases b with
      | false => simpa [vertices,Valid,subtree] using hl p
      | true => simpa [vertices,Valid,subtree] using hr p

theorem mem_edges (S : Tree) (p : Vertex) : p ∈ edges S ↔ Valid S p ∧ p ≠ [] := by
  cases S with
  | leaf x => cases p <;> simp [edges,Valid,subtree]
  | node l r =>
    cases p with
    | nil => simp [edges]
    | cons b p => cases b <;> simp [edges,Valid,subtree,mem_vertices,Valid]

theorem subtreeLabels_mem (S : Tree) (p : Vertex) (x : Nat) :
    x ∈ subtreeLabels S p ↔ ∃ a, LeafAt S a x ∧ Pre p a := by
  cases hs : subtree S p with
  | none =>
    simp only [subtreeLabels,hs,List.not_mem_nil,false_iff]
    rintro ⟨a,ha,⟨q,hq⟩⟩
    have hv : Valid S p := valid_ancestor ha.valid ⟨q,hq⟩
    obtain ⟨s,h⟩ := hv
    simp [hs] at h
  | some s =>
    simp only [subtreeLabels,hs]
    constructor
    · intro hx
      obtain ⟨q,hq⟩ := leaf_exists hx
      refine ⟨p ++ q,?_,List.prefix_append p q⟩
      change subtree S (p ++ q) = some (.leaf x)
      rw [subtree_append hs q]
      exact hq
    · rintro ⟨a,ha,⟨q,hq⟩⟩
      subst a
      have h := ha
      change subtree S (p ++ q) = some (.leaf x) at h
      rw [subtree_append hs q] at h
      exact leafAt_label s q x h

theorem subtreeLabels_subset (S : Tree) (p : Vertex) : subtreeLabels S p ⊆ leaves S := by
  intro x hx
  obtain ⟨a,ha,_⟩ := (subtreeLabels_mem S p x).1 hx
  exact leafAt_label S a x ha

theorem subtree_leaves_sublist (S s : Tree) (p : Vertex) (hs : subtree S p = some s) :
    (leaves s).Sublist (leaves S) := by
  induction S generalizing p with
  | leaf x =>
    cases p with
    | nil => simp [subtree] at hs; subst s; exact List.Sublist.refl _
    | cons b p => simp [subtree] at hs
  | node l r hl hr =>
    cases p with
    | nil => simp [subtree] at hs; subst s; exact List.Sublist.refl _
    | cons b p =>
      cases b with
      | false => exact (hl p hs).trans (List.sublist_append_left _ _)
      | true => exact (hr p hs).trans (List.sublist_append_right _ _)

theorem subtreeLabels_nodup (S : Tree) (p : Vertex) (hn : (leaves S).Nodup) :
    (subtreeLabels S p).Nodup := by
  cases hs : subtree S p with
  | none => simp [subtreeLabels,hs]
  | some s => simpa [subtreeLabels,hs] using hn.sublist (subtree_leaves_sublist S s p hs)

theorem checked_flatten_perm (L : List Nat) (F : List (List Nat))
    (hn : L.Nodup) (hp : partitionCheck L F = true) : F.flatten.Perm L := by
  apply List.perm_iff_count.2
  intro x
  by_cases hx : x ∈ L
  · rw [checked_count L F hp hx,hn.count]
    simp [hx]
  · have hnot : x ∉ F.flatten := by
      intro hm
      obtain ⟨B,hB,hxB⟩ := List.mem_flatten.1 hm
      exact hx (checked_label L F hp hB hxB)
    rw [List.count_eq_zero.2 hnot,List.count_eq_zero.2 hx]

theorem checked_block_nodup (L : List Nat) (F : List (List Nat))
    (hn : L.Nodup) (hp : partitionCheck L F = true) (B : List Nat) (hb : B ∈ F) : B.Nodup :=
  (hn.perm (checked_flatten_perm L F hn hp).symm).sublist (List.sublist_flatten_of_mem hb)

theorem checked_disjoint (L A B : List Nat) (hp : partitionCheck L [A,B] = true) :
    ∀ x, x ∈ A → x ∈ B → False := by
  intro x ha hb
  have hc := checked_count L [A,B] hp (checked_label L [A,B] hp (by simp) ha)
  have hca := List.count_pos_iff.2 ha
  have hcb := List.count_pos_iff.2 hb
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append] at hc
  omega

theorem restrict_members (T : Tree) (A B : List Nat) (he : ∀ x, x ∈ A ↔ x ∈ B) :
    restrict A T = restrict B T := by
  induction T with
  | leaf x => simp [restrict,he x]
  | node l r hl hr => simp only [restrict,hl,hr]

theorem span_members (T : Tree) (A B : List Nat) (he : ∀ x, x ∈ A ↔ x ∈ B) :
    rootedSpan A T = rootedSpan B T := by
  induction T with
  | leaf x => simp [rootedSpan,he x]
  | node l r hl hr => simp only [rootedSpan,hl,hr]

theorem minimal_members (T : Tree) (A B : List Nat) (he : ∀ x, x ∈ A ↔ x ∈ B) :
    minimalVertices A T = minimalVertices B T := by
  induction T with
  | leaf x => simp [minimalVertices,he x]
  | node l r hl hr => simp only [minimalVertices,span_members l A B he,span_members r A B he,hl,hr]

theorem partition_pair_perm (L A B C D : List Nat) (hA : A.Perm C) (hB : B.Perm D) :
    partitionCheck L [A,B] = partitionCheck L [C,D] := by
  have hflat : (A ++ B).Perm (C ++ D) := hA.append hB
  simp only [partitionCheck,List.all_cons,List.all_nil,Bool.and_true,List.flatten_cons,List.flatten_nil,List.append_nil]
  have hnA : A.isEmpty = C.isEmpty := by cases A <;> cases C <;> simp_all
  have hnB : B.isEmpty = D.isEmpty := by cases B <;> cases D <;> simp_all
  rw [hnA,hnB]
  have hc := List.all_congr (l₁ := L) rfl (fun x => congrArg (fun n : Nat => n == 1) (hflat.count_eq x))
  rw [hc,hflat.all_eq]

theorem agreement_pair_perm (T S : Tree) (A B C D : List Nat)
    (hA : A.Perm C) (hB : B.Perm D) : agreement T S [A,B] = agreement T S [C,D] := by
  have ha : ∀ x, x ∈ A ↔ x ∈ C := fun _ => hA.mem_iff
  have hb : ∀ x, x ∈ B ↔ x ∈ D := fun _ => hB.mem_iff
  simp only [agreement,partition_pair_perm _ A B C D hA hB,
    List.all_cons,List.all_nil,Bool.and_true,restrictionAgrees,
    restrict_members T A C ha,restrict_members S A C ha,
    restrict_members T B D hb,restrict_members S B D hb,
    pairwiseEmbeddings,minimal_members T A C ha,minimal_members T B D hb,
    minimal_members S A C ha,minimal_members S B D hb]

theorem agreement_pair_swap (T S : Tree) (A B : List Nat) :
    agreement T S [A,B] = agreement T S [B,A] := by
  have hp : (A ++ B).Perm (B ++ A) := List.perm_append_comm
  have hc : ∀ L, partitionCheck L [A,B] = partitionCheck L [B,A] := by
    intro L
    simp only [partitionCheck,List.all_cons,List.all_nil,Bool.and_true,List.flatten_cons,List.flatten_nil,List.append_nil]
    rw [hp.all_eq]
    have hh : L.all (fun x => (A ++ B).count x == 1) = L.all (fun x => (B ++ A).count x == 1) := by
      exact List.all_congr rfl (fun x => congrArg (fun n : Nat => n == 1) (hp.count_eq x))
    rw [hh]
    ac_rfl
  apply Bool.eq_iff_iff.2
  simp only [agreement,hc (leaves T),hc (leaves S),Bool.and_eq_true,
    pairwiseEmbeddings,List.all_cons,List.all_nil,Bool.and_true,clear_iff]
  rw [clear_symm (minimalVertices A T),clear_symm (minimalVertices A S)]
  simp only [and_comm,and_left_comm,and_assoc]

end Universal233.DepthOne
