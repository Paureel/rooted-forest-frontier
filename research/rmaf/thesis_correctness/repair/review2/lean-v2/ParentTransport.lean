import Std
namespace SecondExchange

variable {V : Type} [DecidableEq V]

def cutParent (cut : V → Bool) (parent : V → Option V) (e : V) : Option V :=
  if cut e then none else parent e

/-- Suppress s with its sole child t. Edge IDs are child vertices; only t's
parent changes, and s is removed from the active-vertex inventory separately. -/
def splice (parent : V → Option V) (s t e : V) : Option V :=
  if e = t then parent s else if e = s then none else parent e

theorem splice_unchanged (parent : V → Option V) (s t e : V)
    (hs : e ≠ s) (ht : e ≠ t) : splice parent s t e = parent e := by
  simp [splice, hs, ht]

/-- Exact maps, not equality of components. Neither incident path edge may
belong to the residual cutset. -/
theorem splice_cut_commute (parent : V → Option V) (cut : V → Bool) (s t : V)
    (hs : cut s = false) (ht : cut t = false) :
    splice (cutParent cut parent) s t = cutParent cut (splice parent s t) := by
  funext e
  by_cases he : e = t
  · subst e; simp [splice, cutParent, hs, ht]
  · by_cases hse : e = s
    · subst e; simp [splice, cutParent, hs, he]
    · simp [splice, cutParent, he, hse]

omit [DecidableEq V] in
theorem cut_union (parent : V → Option V) (b c : V → Bool) :
    cutParent c (cutParent b parent) = cutParent (fun e => b e || c e) parent := by
  funext e
  cases hb : b e <;> cases hc : c e <;> simp [cutParent, hb, hc]

/-- After two legal corridor suppressions, residual cuts give the identical
raw parent map as cutting first and performing the same suppressions. -/
theorem two_splices_cut_commute (parent : V → Option V) (b c : V → Bool)
    (s₁ t₁ s₂ t₂ : V)
    (hs₁ : c s₁ = false) (ht₁ : c t₁ = false)
    (hs₂ : c s₂ = false) (ht₂ : c t₂ = false) :
    cutParent c (splice (splice (cutParent b parent) s₁ t₁) s₂ t₂) =
    splice (splice (cutParent (fun e => b e || c e) parent) s₁ t₁) s₂ t₂ := by
  rw [← splice_cut_commute _ c s₂ t₂ hs₂ ht₂]
  rw [← splice_cut_commute _ c s₁ t₁ hs₁ ht₁]
  rw [cut_union]

/-- A specified outside edge retains its actual endpoints through both
splices. Used for ex, eu, and the incoming edge of v when present. -/
theorem two_splices_unchanged (parent : V → Option V) (s₁ t₁ s₂ t₂ e : V)
    (hs₁ : e ≠ s₁) (ht₁ : e ≠ t₁) (hs₂ : e ≠ s₂) (ht₂ : e ≠ t₂) :
    splice (splice parent s₁ t₁) s₂ t₂ e = parent e := by
  rw [splice_unchanged _ _ _ _ hs₂ ht₂, splice_unchanged _ _ _ _ hs₁ ht₁]

theorem root_absence_preserved (parent : V → Option V) (s₁ t₁ s₂ t₂ v : V)
    (hs₁ : v ≠ s₁) (ht₁ : v ≠ t₁) (hs₂ : v ≠ s₂) (ht₂ : v ≠ t₂)
    (hroot : parent v = none) :
    splice (splice parent s₁ t₁) s₂ t₂ v = none := by
  rw [two_splices_unchanged parent s₁ t₁ s₂ t₂ v hs₁ ht₁ hs₂ ht₂, hroot]

omit [DecidableEq V] in
theorem lift_exact_count (b₁ b₂ : V) (residual full : List V)
    (same_ids : full.Perm (b₁ :: b₂ :: residual)) :
    full.length = 2 + residual.length := by
  have h := same_ids.length_eq
  simp only [List.length_cons] at h
  omega

omit [DecidableEq V] in
theorem lift_nodup (b₁ b₂ : V) (residual : List V)
    (different : b₁ ≠ b₂) (h₁ : b₁ ∉ residual) (h₂ : b₂ ∉ residual)
    (hr : residual.Nodup) : (b₁ :: b₂ :: residual).Nodup := by
  simp [List.nodup_cons, different, h₁, h₂, hr]

#print axioms splice_unchanged
#print axioms splice_cut_commute
#print axioms cut_union
#print axioms two_splices_cut_commute
#print axioms two_splices_unchanged
#print axioms root_absence_preserved
#print axioms lift_exact_count
#print axioms lift_nodup
end SecondExchange
