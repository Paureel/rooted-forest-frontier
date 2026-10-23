import SupportRecovery

namespace TripleDP.Transitions.Restriction
open TripleDP.CostRoute

variable {α I : Type} {l r : BTree α}

theorem recover_closeBoth (A : Family (.node l r) I) (h : OpenBranchLive A)
    (ho : A.boundary = none) :
    Represents (closeBoth (restrict A h false) (restrict A h true)) A (splitMap A) := by
  have hn := no_overlap_closed A ho
  refine ⟨splitMap_injective A hn, splitMap_surjective A, ?_, ?_⟩
  · intro j
    cases j with
    | inl i =>
      have hi : ¬ Live A true i.val := fun hr => hn ⟨i.val, i.property, hr⟩
      simpa [splitMap, ho, closeBoth, closedSupport, restrict] using
        (support_left_exact A h i.val hi).symm
    | inr i =>
      have hi : ¬ Live A false i.val := fun hl => hn ⟨i.val, hl, i.property⟩
      simpa [splitMap, ho, closeBoth, closedSupport, restrict] using
        (support_right_exact A h i.val hi).symm
  · exact ho.symm

theorem recover_extendLeft (A : Family (.node l r) I) (h : OpenBranchLive A)
    (o : I) (ho : A.boundary = some o) (hl : Live A false o) (hr : ¬ Live A true o) :
    Represents (extendLeft (restrict A h false) (restrict A h true) ⟨o, hl⟩
      (restrict_open_boundary A h o ho false hl)) A (splitMap A) := by
  have hn := no_overlap_left A o ho hr
  refine ⟨splitMap_injective A hn, splitMap_surjective A, ?_, ?_⟩
  · intro j
    cases j with
    | inl i =>
      have hi : ¬ Live A true i.val := fun hh => hn ⟨i.val, i.property, hh⟩
      funext a
      simpa [splitMap, ho, extendLeft, adjoinRoot, adjoinRootSupport, closeBoth,
        closedSupport, restrict, Subtype.ext_iff, eq_comm] using
        congrFun (support_left_exact A h i.val hi).symm a
    | inr i =>
      have hi : ¬ Live A false i.val := fun hh => hn ⟨i.val, hh, i.property⟩
      have hio : i.val ≠ o := fun he => hr (he ▸ i.property)
      funext a
      simpa [splitMap, ho, extendLeft, adjoinRoot, adjoinRootSupport, closeBoth,
        closedSupport, restrict, hio, Ne.symm hio] using
        congrFun (support_right_exact A h i.val hi).symm a
  · exact ho.symm

theorem recover_extendRight (A : Family (.node l r) I) (h : OpenBranchLive A)
    (o : I) (ho : A.boundary = some o) (hl : ¬ Live A false o) (hr : Live A true o) :
    Represents (extendRight (restrict A h false) (restrict A h true) ⟨o, hr⟩
      (restrict_open_boundary A h o ho true hr)) A (splitMap A) := by
  have hn := no_overlap_right A o ho hl
  refine ⟨splitMap_injective A hn, splitMap_surjective A, ?_, ?_⟩
  · intro j
    cases j with
    | inl i =>
      have hi : ¬ Live A true i.val := fun hh => hn ⟨i.val, i.property, hh⟩
      have hio : i.val ≠ o := fun he => hl (he ▸ i.property)
      funext a
      simpa [splitMap, ho, extendRight, adjoinRoot, adjoinRootSupport, closeBoth,
        closedSupport, restrict, hio, Ne.symm hio] using
        congrFun (support_left_exact A h i.val hi).symm a
    | inr i =>
      have hi : ¬ Live A false i.val := fun hh => hn ⟨i.val, hh, i.property⟩
      funext a
      simpa [splitMap, ho, extendRight, adjoinRoot, adjoinRootSupport, closeBoth,
        closedSupport, restrict, Subtype.ext_iff, eq_comm] using
        congrFun (support_right_exact A h i.val hi).symm a
  · exact ho.symm

#print axioms recover_closeBoth
#print axioms recover_extendLeft
#print axioms recover_extendRight
end TripleDP.Transitions.Restriction
