import RMAF

namespace RestrictionRoute
open RMAF

/-- The option-level operation executed at an actual tree node. -/
def joinRestricted : Option Tree → Option Tree → Option Tree
  | none, x => x
  | x, none => x
  | some l, some r => some (.node l r)

theorem restrict_node (A : List Nat) (l r : Tree) :
    restrict A (.node l r) = joinRestricted (restrict A l) (restrict A r) := by
  cases hl : restrict A l <;> cases hr : restrict A r <;> simp [restrict, hl, hr, joinRestricted]

theorem joinRestricted_bind (A : List Nat) (l r : Option Tree) :
    (joinRestricted l r).bind (restrict A) =
      joinRestricted (l.bind (restrict A)) (r.bind (restrict A)) := by
  cases l <;> cases r <;> simp [joinRestricted, restrict_node]
  split <;> simp_all

/-- Restricting twice intersects the selected label lists by membership. -/
theorem restrict_associative (t : Tree) (A B : List Nat) :
    (restrict B t).bind (restrict A) = restrict (B.filter (fun x => A.contains x)) t := by
  induction t with
  | leaf x =>
      simp only [restrict]
      by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;>
        simp [restrict, ha, hb]
  | node l r hl hr =>
      simp only [restrict_node, joinRestricted_bind, hl, hr]

theorem restrict_congr (t : Tree) (A B : List Nat)
    (h : ∀ x, x ∈ A ↔ x ∈ B) : restrict A t = restrict B t := by
  induction t with
  | leaf x =>
      have hh : A.contains x = B.contains x := by
        apply Bool.eq_iff_iff.mpr
        simpa only [List.contains_iff_mem] using h x
      simp only [restrict, hh]
  | node l r hl hr => simp only [restrict_node, hl, hr]

/-- Subsets can be restricted directly or through a larger selected set. -/
theorem restrict_associative_subset (t : Tree) (A B : List Nat)
    (h : ∀ x ∈ A, x ∈ B) :
    (restrict B t).bind (restrict A) = restrict A t := by
  rw [restrict_associative]
  apply restrict_congr
  intro x
  simp only [List.mem_filter, List.contains_iff_mem]
  exact ⟨And.right, fun hx => ⟨h x hx, hx⟩⟩

/-- Empty/nonempty outcomes are part of the isomorphism relation. -/
def OptionRootedIso : Option Tree → Option Tree → Prop
  | none, none => True
  | some t, some u => RootedIso t u
  | _, _ => False

theorem joinRestricted_iso {a b c d : Option Tree}
    (hac : OptionRootedIso a c) (hbd : OptionRootedIso b d) :
    OptionRootedIso (joinRestricted a b) (joinRestricted c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [OptionRootedIso, joinRestricted] at *
  all_goals first | contradiction | trivial | exact RootedIso.straight hac hbd

theorem joinRestricted_iso_swapped {a b c d : Option Tree}
    (had : OptionRootedIso a d) (hbc : OptionRootedIso b c) :
    OptionRootedIso (joinRestricted a b) (joinRestricted c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [OptionRootedIso, joinRestricted] at *
  all_goals first | contradiction | trivial | exact RootedIso.swapped had hbc

/-- Rooted label-preserving isomorphism survives pruning and unary suppression. -/
theorem rootedIso_restrict {t u : Tree} (h : RootedIso t u) (A : List Nat) :
    OptionRootedIso (restrict A t) (restrict A u) := by
  induction h with
  | leaf x =>
      simp only [restrict]
      split <;> simp only [OptionRootedIso]
      exact RootedIso.leaf x
  | straight h₁ h₂ ih₁ ih₂ =>
      simp only [restrict_node]
      exact joinRestricted_iso ih₁ ih₂
  | swapped h₁ h₂ ih₁ ih₂ =>
      simp only [restrict_node]
      exact joinRestricted_iso_swapped ih₁ ih₂

theorem joinRestricted_eq_none (a b : Option Tree) :
    joinRestricted a b = none ↔ a = none ∧ b = none := by
  cases a <;> cases b <;> simp [joinRestricted]

theorem restrict_eq_none_iff (t : Tree) (A : List Nat) :
    restrict A t = none ↔ ∀ x ∈ leaves t, x ∉ A := by
  induction t with
  | leaf x => simp [restrict, leaves]
  | node l r hl hr =>
      rw [restrict_node, joinRestricted_eq_none, hl, hr]
      simp only [leaves, List.mem_append, or_imp, forall_and]

theorem restrict_some_of_mem (t : Tree) (A : List Nat) (x : Nat)
    (hxA : x ∈ A) (hxt : x ∈ leaves t) : ∃ s, restrict A t = some s := by
  cases h : restrict A t with
  | none => exact False.elim ((restrict_eq_none_iff t A).mp h x hxt hxA)
  | some s => exact ⟨s, rfl⟩

/-- Restriction agreement is hereditary for any nonempty selected subblock.
The two full trees need not have equal leaf sets or unique labels here. -/
theorem restrictionAgrees_subset (t u : Tree) (A B : List Nat)
    (hAB : ∀ x ∈ A, x ∈ B) (hAt : ∀ x ∈ A, x ∈ leaves t)
    (hA : A ≠ []) (hB : restrictionAgrees t u B = true) :
    restrictionAgrees t u A = true := by
  obtain ⟨x, hx⟩ : ∃ x, x ∈ A := by
    cases A with
    | nil => exact False.elim (hA rfl)
    | cons x xs => exact ⟨x, by simp⟩
  obtain ⟨s, hs⟩ := restrict_some_of_mem t A x hx (hAt x hx)
  cases htB : restrict B t with
  | none => simp [restrictionAgrees, htB] at hB
  | some tb =>
      cases huB : restrict B u with
      | none => simp [restrictionAgrees, huB] at hB
      | some ub =>
          have hiso : RootedIso tb ub := (sameShape_correct tb ub).mp (by
            simpa [restrictionAgrees, htB, huB] using hB)
          have hsub := rootedIso_restrict hiso A
          have htA := restrict_associative_subset t A B hAB
          have huA := restrict_associative_subset u A B hAB
          simp only [htB, Option.bind_some] at htA
          simp only [huB, Option.bind_some] at huA
          rw [htA, huA, hs] at hsub
          cases hu : restrict A u with
          | none => simp [hu, OptionRootedIso] at hsub
          | some v =>
              have hisub : RootedIso s v := by simpa [hu, OptionRootedIso] using hsub
              simpa [restrictionAgrees, hs, hu] using (sameShape_correct s v).mpr hisub

#print axioms restrict_associative
#print axioms restrict_associative_subset
#print axioms rootedIso_restrict
#print axioms restrictionAgrees_subset
end RestrictionRoute
