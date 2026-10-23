import RationalMass

/-! One-shot exact original INPUT color accounting for whole-source calls.
No cardinality, rank, or mass assertion occurs in a structure field. -/
namespace Universal233.WholeSourceMass
open RMAF VertexGeometry SourceCoverage

structure ParentPartition (S : Tree) (A B C : List Nat) : Prop where
  cover : ∀ x, x ∈ leaves S ↔ x ∈ A ∨ x ∈ B ∨ x ∈ C
  ab : ∀ x, x ∈ A → x ∈ B → False
  ac : ∀ x, x ∈ A → x ∈ C → False
  bc : ∀ x, x ∈ B → x ∈ C → False

def taggedColor (A B : List Nat) (ca cb cc : Nat → Nat) (x : Nat) : Nat :=
  if x ∈ A then 3 * ca x else if x ∈ B then 3 * cb x + 1 else 3 * cc x + 2

def localColors (D : List Nat) (f : Nat → Nat) : List Nat := dedupNat (D.map f)

@[simp] theorem mem_localColors (D : List Nat) (f : Nat → Nat) (i : Nat) :
    i ∈ localColors D f ↔ ∃ x, x ∈ D ∧ f x = i := by
  simp [localColors,List.mem_map]

theorem localColors_nodup (D : List Nat) (f : Nat → Nat) :
    (localColors D f).Nodup := dedupNat_nodup _

theorem nodup_map_of_injOn {α β : Type} (L : List α) (f : α → β)
    (hn : L.Nodup)
    (hi : ∀ a, a ∈ L → ∀ b, b ∈ L → f a = f b → a = b) : (L.map f).Nodup := by
  induction L with
  | nil => simp
  | cons a as ih =>
    obtain ⟨hna,hns⟩ := List.nodup_cons.mp hn
    apply List.nodup_cons.mpr
    constructor
    · intro h
      obtain ⟨b,hb,he⟩ := List.mem_map.mp h
      exact hna ((hi b (by simp [hb]) a (by simp) he) ▸ hb)
    · exact ih hns (by intro b hb c hc; exact hi b (by simp [hb]) c (by simp [hc]))

theorem same_members_length {α : Type} (L M : List α) (hL : L.Nodup) (hM : M.Nodup)
    (h : ∀ i, i ∈ L ↔ i ∈ M) : L.length = M.length :=
  ((List.perm_ext_iff_of_nodup hL hM).mpr h).length_eq

def taggedSupports (A B C : List Nat) (ca cb cc : Nat → Nat) : List Nat :=
  ((localColors A ca).map (fun i => 3*i) ++
    (localColors B cb).map (fun i => 3*i+1)) ++
    (localColors C cc).map (fun i => 3*i+2)

theorem taggedSupports_nodup (A B C : List Nat) (ca cb cc : Nat → Nat) :
    (taggedSupports A B C ca cb cc).Nodup := by
  have ha := nodup_map_of_injOn (localColors A ca) (fun i => 3*i)
    (localColors_nodup _ _) (by intros; omega)
  have hb := nodup_map_of_injOn (localColors B cb) (fun i => 3*i+1)
    (localColors_nodup _ _) (by intros; omega)
  have hc := nodup_map_of_injOn (localColors C cc) (fun i => 3*i+2)
    (localColors_nodup _ _) (by intros; omega)
  simp only [taggedSupports,List.nodup_append]
  refine ⟨⟨ha,hb,?_⟩,hc,?_⟩
  · intro x hx y hy
    obtain ⟨a,ha,he⟩ := List.mem_map.mp hx
    obtain ⟨b,hb,hf⟩ := List.mem_map.mp hy
    omega
  · intro x hx y hy
    obtain ⟨c,hc,he⟩ := List.mem_map.mp hy
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨a,ha,hf⟩ := List.mem_map.mp hx; omega
    · obtain ⟨b,hb,hf⟩ := List.mem_map.mp hx; omega

theorem taggedSupports_members (S : Tree) (A B C : List Nat)
    (hp : ParentPartition S A B C) (ca cb cc : Nat → Nat) (i : Nat) :
    i ∈ dedupNat ((leaves S).map (taggedColor A B ca cb cc)) ↔
      i ∈ taggedSupports A B C ca cb cc := by
  simp only [mem_dedupNat,List.mem_map,taggedSupports,List.mem_append]
  constructor
  · rintro ⟨x,hx,rfl⟩
    rcases (hp.cover x).mp hx with hA | hB | hC
    · exact Or.inl (Or.inl ⟨ca x,(mem_localColors _ _ _).mpr ⟨x,hA,rfl⟩,by simp [taggedColor,hA]⟩)
    · exact Or.inl (Or.inr ⟨cb x,(mem_localColors _ _ _).mpr ⟨x,hB,rfl⟩,by simp [taggedColor,hB,show x ∉ A from fun h => hp.ab x h hB]⟩)
    · exact Or.inr ⟨cc x,(mem_localColors _ _ _).mpr ⟨x,hC,rfl⟩,by simp [taggedColor,show x ∉ A from fun h => hp.ac x h hC,show x ∉ B from fun h => hp.bc x h hC]⟩
  · rintro ((⟨a,ha,rfl⟩ | ⟨b,hb,rfl⟩) | ⟨c,hc,rfl⟩)
    · obtain ⟨x,hx,he⟩ := (mem_localColors _ _ _).mp ha
      exact ⟨x,(hp.cover x).mpr (Or.inl hx),by simp [taggedColor,hx,he]⟩
    · obtain ⟨x,hx,he⟩ := (mem_localColors _ _ _).mp hb
      exact ⟨x,(hp.cover x).mpr (Or.inr (Or.inl hx)),by simp [taggedColor,hx,he,show x ∉ A from fun h => hp.ab x h hx]⟩
    · obtain ⟨x,hx,he⟩ := (mem_localColors _ _ _).mp hc
      exact ⟨x,(hp.cover x).mpr (Or.inr (Or.inr hx)),by simp [taggedColor,he,show x ∉ A from fun h => hp.ac x h hx,show x ∉ B from fun h => hp.bc x h hx]⟩

/-- Exact literal original input color count: no implicit color for an empty parent. -/
theorem taggedColor_cardinality (S : Tree) (A B C : List Nat)
    (hp : ParentPartition S A B C) (ca cb cc : Nat → Nat) :
    (dedupNat ((leaves S).map (taggedColor A B ca cb cc))).length =
      (localColors A ca).length + (localColors B cb).length + (localColors C cc).length := by
  have h := same_members_length _ _ (dedupNat_nodup _)
    (taggedSupports_nodup A B C ca cb cc) (taggedSupports_members S A B C hp ca cb cc)
  simpa only [taggedSupports,List.length_append,List.length_map] using h

theorem localColors_zero (D : List Nat) (hn : D ≠ []) :
    (localColors D (fun _ => 0)).length = 1 := by
  have hmem : ∀ i, i ∈ localColors D (fun _ => 0) ↔ i ∈ [0] := by
    intro i
    simp only [mem_localColors,List.mem_singleton]
    constructor
    · rintro ⟨x,hx,rfl⟩; rfl
    · intro he
      cases D with
      | nil => contradiction
      | cons x xs => exact ⟨x,by simp,he.symm⟩
  exact same_members_length _ [0] (localColors_nodup _ _) (by simp) hmem

end Universal233.WholeSourceMass
