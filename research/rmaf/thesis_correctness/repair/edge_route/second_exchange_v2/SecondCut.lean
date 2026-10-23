import ParentTransport
namespace SecondExchange
variable {V : Type} [DecidableEq V]

/-- The root-safe rule on the two-edge x--u path. Both original incident
edges are restored; v is added only when both were cut and v has a parent. -/
def secondCut (cut : V → Bool) (x u v : V) (parentPresent : Bool) (e : V) : Bool :=
  if e = x ∨ e = u then false
  else if cut x = true ∧ cut u = true ∧ parentPresent = true ∧ e = v then true
  else cut e

theorem secondCut_away (cut : V → Bool) (x u v e : V) (parentPresent : Bool)
    (hx : e ≠ x) (hu : e ≠ u) (hv : e ≠ v) :
    secondCut cut x u v parentPresent e = cut e := by
  simp [secondCut, hx, hu, hv]

theorem secondCut_path_removed (cut : V → Bool) (x u v : V) (parentPresent : Bool) :
    secondCut cut x u v parentPresent x = false ∧
      secondCut cut x u v parentPresent u = false := by
  simp [secondCut]

theorem secondCut_provenance (cut : V → Bool) (x u v e : V) (parentPresent : Bool)
    (h : secondCut cut x u v parentPresent e = true) :
    cut e = true ∨ (e = v ∧ parentPresent = true ∧ cut x = true ∧ cut u = true) := by
  unfold secondCut at h
  split at h
  · contradiction
  · split at h
    · simp_all
    · exact Or.inl h

theorem secondCut_root_no_addition (cut : V → Bool) (x u v e : V)
    (h : secondCut cut x u v false e = true) : cut e = true := by
  rcases secondCut_provenance cut x u v e false h with hc | hp
  · exact hc
  · simp at hp

/-- A corridor incidence remains uncut after the second exchange when it
is outside the three possible modified edge IDs. -/
theorem secondCut_preserves_protected (cut : V → Bool) (x u v e : V)
    (parentPresent : Bool) (he : cut e = false)
    (hx : e ≠ x) (hu : e ≠ u) (hv : e ≠ v) :
    secondCut cut x u v parentPresent e = false := by
  rw [secondCut_away cut x u v e parentPresent hx hu hv, he]

#print axioms secondCut_away
#print axioms secondCut_path_removed
#print axioms secondCut_provenance
#print axioms secondCut_root_no_addition
#print axioms secondCut_preserves_protected
end SecondExchange
