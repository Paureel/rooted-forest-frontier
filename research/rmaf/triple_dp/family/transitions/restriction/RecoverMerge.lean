import SupportRecovery

namespace TripleDP.Transitions.Restriction
open TripleDP.CostRoute

variable {α I : Type} {l r : BTree α}

def mergeMap (A : Family (.node l r) I) (o : I) (hr : Live A true o) :
    MergeIndex (LiveIndex A false) (⟨o, hr⟩ : LiveIndex A true) → I
  | .inl i => i.val
  | .inr j => j.val.val

theorem mergeMap_surjective (A : Family (.node l r) I) (o : I)
    (hl : Live A false o) (hr : Live A true o) :
    ∀ i, ∃ j, mergeMap A o hr j = i := by
  classical
  intro i
  by_cases hi : Live A false i
  · exact ⟨.inl ⟨i, hi⟩, rfl⟩
  · have hj : Live A true i := (live_some_child A i).resolve_left hi
    have hn : (⟨i, hj⟩ : LiveIndex A true) ≠ ⟨o, hr⟩ := by
      intro he
      have hv : i = o := congrArg Subtype.val he
      exact hi (hv.symm ▸ hl)
    exact ⟨.inr ⟨⟨i, hj⟩, hn⟩, rfl⟩

theorem right_survivor_not_left (A : Family (.node l r) I) (o : I)
    (ho : A.boundary = some o) (hr : Live A true o)
    (j : {j : LiveIndex A true // j ≠ ⟨o, hr⟩}) : ¬ Live A false j.val.val := by
  intro hj
  have he : j.val.val = o := Option.some.inj
    ((both_live_boundary A j.val.val hj j.val.property).symm.trans ho)
  exact j.property (Subtype.ext he)

theorem mergeMap_injective (A : Family (.node l r) I) (o : I)
    (ho : A.boundary = some o) (hr : Live A true o) :
    ∀ j k, mergeMap A o hr j = mergeMap A o hr k → j = k := by
  intro j k he
  cases j with
  | inl j =>
    cases k with
    | inl k => exact congrArg Sum.inl (Subtype.ext he)
    | inr k =>
      change j.val = k.val.val at he
      exact False.elim (right_survivor_not_left A o ho hr k (he ▸ j.property))
  | inr j =>
    cases k with
    | inl k =>
      change j.val.val = k.val at he
      exact False.elim (right_survivor_not_left A o ho hr j (he.symm ▸ k.property))
    | inr k => exact congrArg Sum.inr (Subtype.ext (Subtype.ext he))

noncomputable def rejoin (A : Family (.node l r) I) (h : OpenBranchLive A)
    (o : I) (ho : A.boundary = some o) (hl : Live A false o) (hr : Live A true o) :
    Family (.node l r) (MergeIndex (LiveIndex A false) (⟨o, hr⟩ : LiveIndex A true)) := by
  classical
  exact merge (restrict A h false) (restrict A h true) ⟨o, hl⟩ ⟨o, hr⟩
    (restrict_open_boundary A h o ho false hl) (restrict_open_boundary A h o ho true hr)

theorem recover_merge (A : Family (.node l r) I) (h : OpenBranchLive A)
    (o : I) (ho : A.boundary = some o) (hl : Live A false o) (hr : Live A true o) :
    Represents (rejoin A h o ho hl hr) A (mergeMap A o hr) := by
  classical
  refine ⟨mergeMap_injective A o ho hr, mergeMap_surjective A o hl hr, ?_, ?_⟩
  · intro j
    funext a
    apply propext
    cases j with
    | inl i =>
      cases a with
      | nil =>
        simp [rejoin, merge, mergeMap, A.root_spec, ho, Subtype.ext_iff, eq_comm]
      | cons side a =>
        cases side with
        | false => simp [rejoin, merge, mergeMap, restrict]
        | true =>
          change mergeSupport (restrict A h false) (restrict A h true) ⟨o, hl⟩ ⟨o, hr⟩
            (.inl i) (true :: a) ↔ A.support i.val (true :: a)
          rw [mergeSupport_left_right]
          change (i = ⟨o, hl⟩ ∧ A.support o (true :: a)) ↔ A.support i.val (true :: a)
          constructor
          · rintro ⟨rfl, ha⟩; exact ha
          · intro ha
            have hi : i.val = o := Option.some.inj
              ((both_live_boundary A i.val i.property
                (occupied_live A h i.val true ⟨a, ha⟩)).symm.trans ho)
            exact ⟨Subtype.ext hi, hi ▸ ha⟩
    | inr j =>
      cases a with
      | nil =>
        have hn : j.val.val ≠ o := fun he => j.property (Subtype.ext he)
        simp [rejoin, merge, mergeMap, A.root_spec, ho, Ne.symm hn]
      | cons side a =>
        cases side with
        | false =>
          have hn := not_live_no_support A h j.val.val false
            (right_survivor_not_left A o ho hr j) a
          simp [rejoin, merge, mergeMap, hn]
        | true => simp [rejoin, merge, mergeMap, restrict]
  · exact ho.symm

#print axioms mergeMap_surjective
#print axioms right_survivor_not_left
#print axioms mergeMap_injective
#print axioms rejoin
#print axioms recover_merge
end TripleDP.Transitions.Restriction
