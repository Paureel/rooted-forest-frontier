import StateEmbedding

namespace RestrictionBridge
open RMAF
def contained (B U : List Nat) : Bool := B.all (U.contains ·)
def family (U : List Nat) (F : List (List Nat)) := F.filter (contained · U)
def Refines (F Q : List (List Nat)) : Prop := ∀ B ∈ F, ∃ U ∈ Q, B ⊆ U
@[simp] theorem contained_iff (B U : List Nat) : contained B U = true ↔ B ⊆ U := by
  simp [contained,List.all_eq_true,List.subset_def]
@[simp] theorem mem_family (B U : List Nat) (F : List (List Nat)) :
    B ∈ family U F ↔ B ∈ F ∧ B ⊆ U := by simp [family]

theorem checked_nonempty (labels : List Nat) (F : List (List Nat))
    (hp : partitionCheck labels F = true) : ∀ B ∈ F, B ≠ [] := by
  simp only [partitionCheck,Bool.and_eq_true] at hp
  intro B hb
  have hh := List.all_eq_true.1 hp.1.1 B hb
  simpa using hh

theorem checked_label (labels : List Nat) (F : List (List Nat))
    (hp : partitionCheck labels F = true) {B : List Nat} (hB : B ∈ F)
    {x : Nat} (hx : x ∈ B) : x ∈ labels := by
  simp only [partitionCheck,Bool.and_eq_true] at hp
  exact List.contains_iff_mem.1 (List.all_eq_true.1 hp.2 x (List.mem_flatten.2 ⟨B,hB,hx⟩))

theorem checked_count (labels : List Nat) (F : List (List Nat))
    (hp : partitionCheck labels F = true) {x : Nat} (hx : x ∈ labels) :
    F.flatten.count x = 1 := by
  simp only [partitionCheck,Bool.and_eq_true] at hp
  exact beq_iff_eq.1 (List.all_eq_true.1 hp.1.2 x hx)

theorem checked_covers (labels : List Nat) (F : List (List Nat))
    (hp : partitionCheck labels F = true) {x : Nat} (hx : x ∈ labels) :
    ∃ B ∈ F, x ∈ B := by
  apply List.mem_flatten.1
  apply List.count_pos_iff.1
  rw [checked_count labels F hp hx]
  decide

theorem checked_labels_iff (L M : List Nat) (F : List (List Nat))
    (hL : partitionCheck L F = true) (hM : partitionCheck M F = true) :
    ∀ x, x ∈ L ↔ x ∈ M := by
  intro x
  constructor
  · intro hx; obtain ⟨B,hB,hx⟩ := checked_covers L F hL hx
    exact checked_label M F hM hB hx
  · intro hx; obtain ⟨B,hB,hx⟩ := checked_covers M F hM hx
    exact checked_label L F hL hB hx

theorem unique_label_owner (Q : List (List Nat)) (x : Nat) (hc : Q.flatten.count x = 1) :
    ∃ U ∈ Q, x ∈ U ∧ Q.count U = 1 ∧ ∀ V ∈ Q, x ∈ V → V = U := by
  induction Q with
  | nil => simp at hc
  | cons A Q ih =>
    simp only [List.flatten_cons,List.count_append] at hc
    by_cases hx : x ∈ A
    · have ha : 0 < A.count x := List.count_pos_iff.2 hx
      have hz : Q.flatten.count x = 0 := by omega
      have hnot : ∀ V ∈ Q, x ∉ V := by
        intro V hv hxm
        have : x ∈ Q.flatten := List.mem_flatten.2 ⟨V,hv,hxm⟩
        have hpos := List.count_pos_iff.2 this
        omega
      have han : A ∉ Q := fun hm => hnot A hm hx
      refine ⟨A,by simp,hx,?_,?_⟩
      · simp [List.count_eq_zero.2 han]
      · intro V hv hxv
        rcases List.mem_cons.1 hv with he | hm
        · exact he
        · exact False.elim (hnot V hm hxv)
    · have hz : A.count x = 0 := List.count_eq_zero.2 hx
      obtain ⟨U,hu,hxu,hcu,hone⟩ := ih (by omega)
      have hne : A ≠ U := by intro he; subst A; exact hx hxu
      refine ⟨U,by simp [hu],hxu,?_,?_⟩
      · simp [List.count_cons,hne,hcu]
      · intro V hv hxv
        rcases List.mem_cons.1 hv with he | hm
        · subst V; exact False.elim (hx hxv)
        · exact hone V hm hxv

theorem count_family_flatten (F : List (List Nat)) (U : List Nat) (x : Nat)
    (owners : ∀ B ∈ F, x ∈ B → B ⊆ U) :
    (family U F).flatten.count x = F.flatten.count x := by
  induction F with
  | nil => simp [family]
  | cons B F ih =>
    have ht : ∀ C ∈ F, x ∈ C → C ⊆ U := fun C hc => owners C (by simp [hc])
    have hi : (F.filter (contained · U)).flatten.count x = F.flatten.count x := ih ht
    by_cases hb : B ⊆ U
    · have hh : contained B U = true := (contained_iff B U).2 hb
      simpa [family,hh] using congrArg (fun n => B.count x + n) hi
    · have hh : contained B U = false := by cases h : contained B U <;> simp_all
      have hx : x ∉ B := fun hm => hb (owners B (by simp) hm)
      simpa [family,hh,List.count_eq_zero.2 hx] using hi

theorem local_partition (t u : Tree) (U : List Nat) (F Q : List (List Nat))
    (hr : restrict U t = some u) (hF : partitionCheck (leaves t) F = true)
    (hQ : partitionCheck (leaves t) Q = true) (href : Refines F Q) (hU : U ∈ Q) :
    partitionCheck (leaves u) (family U F) = true := by
  simp only [partitionCheck,Bool.and_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · apply List.all_eq_true.2
    intro B hB
    have hn := checked_nonempty (leaves t) F hF B (mem_family B U F |>.1 hB).1
    simpa using hn
  · apply List.all_eq_true.2
    intro x hx
    obtain ⟨hxt,hxu⟩ := (restricted_labels_exact t u U hr).1 hx
    have hcount := checked_count (leaves t) Q hQ hxt
    obtain ⟨V,hV,hxV,hcV,unique⟩ := unique_label_owner Q x hcount
    have hUV := unique U hU hxu
    have owners : ∀ B ∈ F, x ∈ B → B ⊆ U := by
      intro B hB hxB
      obtain ⟨W,hW,hBW⟩ := href B hB
      have hWV := unique W hW (hBW hxB)
      simpa [hWV,hUV] using hBW
    apply beq_iff_eq.2
    rw [count_family_flatten F U x owners,checked_count (leaves t) F hF hxt]
  · apply List.all_eq_true.2
    intro x hx
    obtain ⟨B,hB,hxB⟩ := List.mem_flatten.1 hx
    obtain ⟨hBF,hBU⟩ := (mem_family B U F).1 hB
    apply List.contains_iff_mem.2
    exact (restricted_labels_exact t u U hr).2 ⟨checked_label (leaves t) F hF hBF hxB,hBU hxB⟩

end RestrictionBridge
