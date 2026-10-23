import Descendant
namespace BinaryExchange
open RMAF VertexGeometry
abbrev Sub (C A : List Nat) : Prop := ∀ x, x ∈ C → x ∈ A
abbrev Disj (t : Tree) (C E : List Nat) : Prop :=
  ∀ v, ¬(Hull (selectedLeaves C t) v ∧ Hull (selectedLeaves E t) v)

theorem hull_mono (t : Tree) (C A : List Nat) (h : Sub C A) :
    ∀ v, Hull (selectedLeaves C t) v → Hull (selectedLeaves A t) v := by
  rintro v ⟨a,b,ha,hb,hp⟩
  exact ⟨a,b,selected_leaves_mono C A t h a ha,selected_leaves_mono C A t h b hb,hp⟩

theorem disj_symm {t C E} (h : Disj t C E) : Disj t E C := by
  intro v hv; exact h v ⟨hv.2,hv.1⟩

theorem disj_mono {t C E A B} (h : Disj t A B) (hc : Sub C A) (he : Sub E B) : Disj t C E := by
  intro v hv; exact h v ⟨hull_mono t C A hc v hv.1,hull_mono t E B he v hv.2⟩

theorem pairwise_mem {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a)
    (F : List α) (hp : F.Pairwise R) (a b : α) (ha : a ∈ F) (hb : b ∈ F) (hne : a ≠ b) : R a b := by
  induction F with
  | nil => simp at ha
  | cons c cs ih =>
    obtain ⟨hc,hcs⟩ := List.pairwise_cons.1 hp
    rcases List.mem_cons.1 ha with ha | ha
    · subst a
      rcases List.mem_cons.1 hb with hb | hb
      · exact False.elim (hne hb.symm)
      · exact hc b hb
    · rcases List.mem_cons.1 hb with hb | hb
      · subst b; exact hs c a (hc a ha)
      · exact ih hcs ha hb

theorem agreement_parts (s t : Tree) (F : List (List Nat)) (h : agreement s t F = true) :
    partitionCheck (leaves s) F = true ∧ partitionCheck (leaves t) F = true ∧
    (∀ C, C ∈ F → restrictionAgrees s t C = true) ∧ F.Pairwise (Disj s) ∧ F.Pairwise (Disj t) := by
  simpa only [agreement,Bool.and_eq_true,List.all_eq_true,executable_pairwiseEmbeddings,and_assoc,Disj] using h

theorem isEmpty_false {α : Type} (L : List α) : L.isEmpty = false ↔ L ≠ [] := by
  cases L <;> simp

theorem partition_parts (L : List Nat) (F : List (List Nat)) (h : partitionCheck L F = true) :
    (∀ C, C ∈ F → C ≠ []) ∧ (∀ x, x ∈ L → F.flatten.count x = 1) ∧
    (∀ x, x ∈ F.flatten → x ∈ L) := by
  simpa only [partitionCheck,Bool.and_eq_true,List.all_eq_true,Bool.not_eq_true',
    isEmpty_false,beq_iff_eq,List.contains_iff_mem,and_assoc] using h

theorem partition_intro (L : List Nat) (F : List (List Nat))
    (hn : ∀ C, C ∈ F → C ≠ []) (hc : ∀ x, x ∈ L → F.flatten.count x = 1)
    (hl : ∀ x, x ∈ F.flatten → x ∈ L) : partitionCheck L F = true := by
  simpa only [partitionCheck,Bool.and_eq_true,List.all_eq_true,Bool.not_eq_true',
    isEmpty_false,beq_iff_eq,List.contains_iff_mem,and_assoc] using And.intro hn (And.intro hc hl)

theorem partition_count (L : List Nat) (F : List (List Nat)) (h : partitionCheck L F = true) (x) :
    F.flatten.count x = if x ∈ L then 1 else 0 := by
  obtain ⟨hn,hc,hl⟩ := partition_parts L F h
  by_cases hx : x ∈ L
  · simp [hx,hc x hx]
  · simp only [hx,ite_false]
    exact List.count_eq_zero.2 (fun hm => hx (hl x hm))

theorem partition_mem (L : List Nat) (F : List (List Nat)) (h : partitionCheck L F = true) (x) :
    x ∈ F.flatten ↔ x ∈ L := by
  rw [← List.count_pos_iff,partition_count L F h]
  by_cases hx : x ∈ L <;> simp [hx]

theorem partition_sub (L : List Nat) (F : List (List Nat)) (h : partitionCheck L F = true)
    (C) (hc : C ∈ F) : Sub C L := by
  intro x hx; exact (partition_parts L F h).2.2 x (List.mem_flatten.2 ⟨C,hc,hx⟩)

def split (C : List Nat) (q : Nat → Bool) : List (List Nat) :=
  [yes C q,no C q].filter (fun b => !b.isEmpty)

theorem mem_split (C E : List Nat) (q : Nat → Bool) :
    E ∈ split C q ↔ (E = yes C q ∨ E = no C q) ∧ E ≠ [] := by
  simp only [split,List.mem_filter,List.mem_cons,List.not_mem_nil,or_false,
    Bool.not_eq_true',isEmpty_false]

theorem split_sub (C E : List Nat) (q : Nat → Bool) (he : E ∈ split C q) : Sub E C := by
  rcases (mem_split C E q).1 he with ⟨h,_⟩
  rcases h with rfl | rfl <;> intro x hx <;> exact (List.mem_filter.1 hx).1

theorem split_count (C : List Nat) (q : Nat → Bool) (x : Nat) :
    (split C q).flatten.count x = C.count x := by
  have hsum : (yes C q).count x + (no C q).count x = C.count x := by
    induction C with
    | nil => simp [yes,no]
    | cons a as ih =>
      cases hq : q a <;> simp [yes,no,hq,List.count_cons] at ih ⊢ <;> omega
  by_cases hy : yes C q = [] <;> by_cases hn : no C q = [] <;>
    simp [split,hy,hn,List.count_append] at * <;> omega

theorem split_mono (C : List Nat) (q : Nat → Bool) (E) (he : E ∈ split C q) :
    (∀ x, x ∈ E → q x = true) ∨ (∀ x, x ∈ E → q x = false) := by
  rcases (mem_split C E q).1 he with ⟨h,_⟩
  rcases h with rfl | rfl
  · exact Or.inl (by intro x hx; exact (List.mem_filter.1 hx).2)
  · exact Or.inr (by intro x hx; have hh := (List.mem_filter.1 hx).2; simpa using hh)

theorem split_pairwise (t : Tree) (C : List Nat) (q : Nat → Bool)
    (hd : Disj t (yes C q) (no C q)) : (split C q).Pairwise (Disj t) := by
  apply List.Pairwise.filter
  apply List.pairwise_cons.2
  refine ⟨?_,by simp⟩
  intro E he
  have he' : E = no C q := by simpa using he
  subst E
  exact hd

def splitAll (V : List (List Nat)) (q : Nat → Bool) := V.flatMap (fun C => split C q)

theorem splitAll_count (V : List (List Nat)) (q : Nat → Bool) (x) :
    (splitAll V q).flatten.count x = V.flatten.count x := by
  induction V with
  | nil => simp [splitAll]
  | cons C V ih =>
    simp only [splitAll] at ih ⊢
    simpa only [List.flatMap_cons,List.flatten_append,List.flatten_cons,List.count_append,split_count] using congrArg (fun n => C.count x + n) ih

theorem splitAll_nonempty (V : List (List Nat)) (q : Nat → Bool) :
    ∀ E, E ∈ splitAll V q → E ≠ [] := by
  intro E he
  obtain ⟨C,hC,hE⟩ := List.mem_flatMap.1 he
  exact ((mem_split C E q).1 hE).2

theorem splitAll_labels (V : List (List Nat)) (q : Nat → Bool) (x) :
    x ∈ (splitAll V q).flatten ↔ x ∈ V.flatten := by
  rw [← List.count_pos_iff,splitAll_count, List.count_pos_iff]

theorem splitAll_pairwise (t : Tree) (V : List (List Nat)) (q : Nat → Bool)
    (hp : V.Pairwise (Disj t)) (hs : ∀ C, C ∈ V → Disj t (yes C q) (no C q)) :
    (splitAll V q).Pairwise (Disj t) := by
  induction V with
  | nil => simp [splitAll]
  | cons C V ih =>
    obtain ⟨hc,hv⟩ := List.pairwise_cons.1 hp
    rw [splitAll,List.flatMap_cons,List.pairwise_append]
    refine ⟨split_pairwise t C q (hs C (by simp)),ih hv (by intro E he; exact hs E (by simp [he])),?_⟩
    intro E hE G hG
    obtain ⟨B,hB,hGB⟩ := List.mem_flatMap.1 hG
    exact disj_mono (hc B hB) (split_sub C E q hE) (split_sub B G q hGB)
end BinaryExchange
