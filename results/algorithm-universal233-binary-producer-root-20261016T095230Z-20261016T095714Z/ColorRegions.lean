import ColorDP

namespace AllGoodDP
open RMAF

-- The first list is the component containing this root. It may be empty.
-- Every detached component, including a leafless one, remains in the second
-- list until the final nonempty filter. Thus disappearance is never unpaid.
def split : Paint → List Nat × List (List Nat)
  | .leaf x _ => ([x],[])
  | .node c l r =>
    let a := split l
    let b := split r
    let la := if c == root l then a.1 else []
    let lb := if c == root r then b.1 else []
    let fa := if c == root l then a.2 else a.1 :: a.2
    let fb := if c == root r then b.2 else b.1 :: b.2
    (la ++ lb, fa ++ fb)

def rawBlocks (p : Paint) : List (List Nat) := (split p).1 :: (split p).2
def blocks (p : Paint) : List (List Nat) := (rawBlocks p).filter (fun b => !b.isEmpty)

theorem split_count (p : Paint) (x : Nat) :
    (split p).1.count x + (split p).2.flatten.count x = (leaves (erase p)).count x := by
  induction p with
  | leaf y c => simp [split,erase,leaves]
  | node c l r hl hr =>
    cases hcl : c == root l <;> cases hcr : c == root r <;>
      simp [split,hcl,hcr,erase,leaves,List.count_append] at * <;> omega

theorem raw_count (p : Paint) (x : Nat) :
    (rawBlocks p).flatten.count x = (leaves (erase p)).count x := by
  simpa [rawBlocks,List.count_append] using split_count p x

theorem flatten_nonempty_filter (F : List (List Nat)) :
    (F.filter (fun b => !b.isEmpty)).flatten = F.flatten := by
  induction F with
  | nil => rfl
  | cons B F ih => cases B <;> simp_all

theorem blocks_flatten (p : Paint) : (blocks p).flatten = (rawBlocks p).flatten :=
  flatten_nonempty_filter _

theorem blocks_count (p : Paint) (x : Nat) :
    (blocks p).flatten.count x = (leaves (erase p)).count x := by
  rw [blocks_flatten,raw_count]

theorem blocks_labels (p : Paint) (x : Nat) :
    x ∈ (blocks p).flatten ↔ x ∈ leaves (erase p) := by
  rw [←List.count_pos_iff,←List.count_pos_iff,blocks_count]

theorem blocks_nonempty (p : Paint) (B : List Nat) (hB : B ∈ blocks p) : B ≠ [] := by
  have hh := (List.mem_filter.1 hB).2
  simpa using hh

theorem blocks_partition (p : Paint) (hn : (leaves (erase p)).Nodup) :
    partitionCheck (leaves (erase p)) (blocks p) = true := by
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro B hB
    have hb := blocks_nonempty p B hB
    simpa using hb
  · intro x hx
    apply beq_iff_eq.2
    rw [blocks_count]
    exact hn.count_of_mem hx
  · intro x hx
    exact List.contains_iff_mem.2 ((blocks_labels p x).1 hx)

theorem split_length (p : Paint) : (split p).2.length = changes p := by
  induction p with
  | leaf x c => rfl
  | node c l r hl hr =>
    cases hcl : c == root l <;> cases hcr : c == root r <;>
      simp [split,changes,delta,hcl,hcr] at * <;> omega

theorem raw_length (p : Paint) : (rawBlocks p).length = changes p + 1 := by
  simp [rawBlocks,split_length]

theorem blocks_length (p : Paint) : (blocks p).length ≤ changes p + 1 := by
  rw [←raw_length]
  exact List.length_filter_le _ _

def Mono (owner : Nat → Nat) (c : Nat) (B : List Nat) : Prop :=
  ∀ x ∈ B, owner x = c

theorem mono_append (owner : Nat → Nat) (c : Nat) (B C : List Nat) :
    Mono owner c (B ++ C) ↔ Mono owner c B ∧ Mono owner c C := by
  simp only [Mono,List.mem_append]
  constructor
  · intro h; exact ⟨fun x hx => h x (Or.inl hx),fun x hx => h x (Or.inr hx)⟩
  · rintro ⟨hB,hC⟩ x (hx | hx)
    · exact hB x hx
    · exact hC x hx

theorem split_mono {cs owner t p} (hv : Valid cs owner t p) :
    root p ∈ cs ∧ Mono owner (root p) (split p).1 ∧
    ∀ B ∈ (split p).2, ∃ c ∈ cs, Mono owner c B := by
  induction hv with
  | leaf x hc => simp [root,split,Mono,hc]
  | @node t u p q c hc hp hq ihp ihq =>
    refine ⟨hc,?_,?_⟩
    · apply (mono_append owner c _ _).2
      constructor
      · by_cases he : c = root p
        · simpa [split,he] using he.symm ▸ ihp.2.1
        · simp [he,Mono]
      · by_cases he : c = root q
        · simpa [split,he] using he.symm ▸ ihq.2.1
        · simp [he,Mono]
    · intro B hB
      have hm : B ∈ (if c == root p then (split p).2 else (split p).1 :: (split p).2) ∨
          B ∈ (if c == root q then (split q).2 else (split q).1 :: (split q).2) := by
        simpa [split] using hB
      rcases hm with hm | hm
      · by_cases he : c = root p
        · exact ihp.2.2 B (by simpa [he] using hm)
        · have hh : (c == root p) = false := by simp [he]
          simp only [hh,Bool.false_eq_true,ite_false,List.mem_cons] at hm
          rcases hm with rfl | hm
          · exact ⟨root p,ihp.1,ihp.2.1⟩
          · exact ihp.2.2 B hm
      · by_cases he : c = root q
        · exact ihq.2.2 B (by simpa [he] using hm)
        · have hh : (c == root q) = false := by simp [he]
          simp only [hh,Bool.false_eq_true,ite_false,List.mem_cons] at hm
          rcases hm with rfl | hm
          · exact ⟨root q,ihq.1,ihq.2.1⟩
          · exact ihq.2.2 B hm

theorem blocks_mono {cs owner t p} (hv : Valid cs owner t p) :
    ∀ B ∈ blocks p, ∃ c ∈ cs, Mono owner c B := by
  have hs := split_mono hv
  intro B hB
  have hm : B = (split p).1 ∨ B ∈ (split p).2 := by
    simpa [rawBlocks] using (List.mem_filter.1 hB).1
  rcases hm with rfl | hm
  · exact ⟨root p,hs.1,hs.2.1⟩
  · exact hs.2.2 B hm

end AllGoodDP
