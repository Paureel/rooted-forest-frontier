import Std

/- GLOBAL-C generic packing certificate.
   The source-tree interpretation of conflicts is deliberately separate.
   This file proves a finite combinatorial statement with no custom axioms. -/
namespace GlobalConflict

def Hits {α : Type} (cuts edgeSet : List α) : Prop :=
  ∃ x, x ∈ edgeSet ∧ x ∈ cuts

def DisjointPacking {α : Type} (family : List (List α)) : Prop :=
  family.Pairwise (fun h g => ∀ x, x ∈ h → x ∈ g → False)

def replaceEdge {α : Type} [DecidableEq α] (cuts : List α) (e f : α) : List α :=
  cuts.map (fun x => if x = e then f else x)

theorem dominancePreservesHitting {α : Type} [DecidableEq α]
    (family : List (List α)) (cuts : List α) (e f : α)
    (dominates : ∀ h ∈ family, e ∈ h → f ∈ h)
    (hit : ∀ h ∈ family, Hits cuts h) :
    ∀ h ∈ family, Hits (replaceEdge cuts e f) h := by
  intro h hh
  obtain ⟨x, hxh, hxc⟩ := hit h hh
  by_cases he : x = e
  · subst x
    refine ⟨f, dominates h hh hxh, ?_⟩
    apply List.mem_map.mpr
    exact ⟨e, hxc, by simp⟩
  · refine ⟨x, hxh, ?_⟩
    apply List.mem_map.mpr
    exact ⟨x, hxc, by simp [he]⟩

theorem replaceEdgeLength {α : Type} [DecidableEq α]
    (cuts : List α) (e f : α) : (replaceEdge cuts e f).length = cuts.length := by
  simp [replaceEdge]

theorem distinctRepresentatives {α : Type} (family : List (List α))
    (cuts : List α) (hd : DisjointPacking family)
    (hh : ∀ h ∈ family, Hits cuts h) :
    ∃ witnesses : List α,
      witnesses.length = family.length ∧ witnesses.Nodup ∧
      witnesses ⊆ cuts ∧
      (∀ x ∈ witnesses, ∃ h ∈ family, x ∈ h) := by
  induction family with
  | nil =>
    exact ⟨[], by simp⟩
  | cons h hs ih =>
    obtain ⟨x, hxh, hxc⟩ := hh h (by simp)
    have hp : (∀ g ∈ hs, ∀ y, y ∈ h → y ∈ g → False) ∧
        DisjointPacking hs := by
      simpa [DisjointPacking, List.pairwise_cons] using hd
    have hhTail : ∀ g ∈ hs, Hits cuts g := by
      intro g hg
      exact hh g (by simp [hg])
    obtain ⟨ws, hlen, hnodup, hsub, hsource⟩ := ih hp.2 hhTail
    have hxnot : x ∉ ws := by
      intro hxws
      obtain ⟨g, hg, hxg⟩ := hsource x hxws
      exact hp.1 g hg x hxh hxg
    refine ⟨x :: ws, by simp [hlen], ?_, ?_, ?_⟩
    · simp [List.nodup_cons, hxnot, hnodup]
    · intro y hy
      simp only [List.mem_cons] at hy
      cases hy with
      | inl he => simpa [he] using hxc
      | inr hy => exact hsub hy
    · intro y hy
      simp only [List.mem_cons] at hy
      cases hy with
      | inl he => exact ⟨h, by simp, by simpa [he] using hxh⟩
      | inr hy =>
        obtain ⟨g, hg, hyg⟩ := hsource y hy
        exact ⟨g, by simp [hg], hyg⟩

theorem packingLowerBound {α : Type} (family : List (List α))
    (cuts : List α) (hd : DisjointPacking family)
    (hh : ∀ h ∈ family, Hits cuts h) : family.length ≤ cuts.length := by
  obtain ⟨ws, hlen, hn, hs, _⟩ := distinctRepresentatives family cuts hd hh
  have hb := hn.length_le_of_subset hs
  simpa [hlen] using hb

theorem saturatedOptimal {α : Type} (valid : List α → Prop)
    (family : List (List α)) (chosen : List α)
    (hd : DisjointPacking family)
    (sound : ∀ cuts, valid cuts → ∀ h ∈ family, Hits cuts h)
    (hv : valid chosen) (saturated : chosen.length = family.length) :
    valid chosen ∧ ∀ cuts, valid cuts → chosen.length ≤ cuts.length := by
  refine ⟨hv, ?_⟩
  intro cuts hc
  rw [saturated]
  exact packingLowerBound family cuts hd (sound cuts hc)

theorem halfBudgetFromChargedWitness (budget precuts localCost : Nat)
    (charged : precuts + localCost ≤ budget) (halfCuts : budget ≤ 2 * precuts) :
    2 * localCost ≤ budget := by
  omega

def triangleFamily : List (List Nat) := [[0,1], [1,2], [0,2]]

theorem triangleTwoCutsHit : ∀ h ∈ triangleFamily, Hits [0,1] h := by
  intro h hh
  simp [triangleFamily] at hh
  rcases hh with rfl | rfl | rfl
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩

theorem triangleNoSingleton :
    ¬ (∃ x : Fin 3, ∀ h ∈ triangleFamily, Hits [x.val] h) := by
  intro hh
  obtain ⟨x, hx⟩ := hh
  have h01 := hx [0,1] (by simp [triangleFamily])
  have h12 := hx [1,2] (by simp [triangleFamily])
  have h02 := hx [0,2] (by simp [triangleFamily])
  simp [Hits] at h01 h12 h02
  omega

theorem trianglePairsIntersect :
    ∀ h ∈ triangleFamily, ∀ g ∈ triangleFamily,
      ∃ x, x ∈ h ∧ x ∈ g := by
  decide

#print axioms distinctRepresentatives
#print axioms dominancePreservesHitting
#print axioms replaceEdgeLength
#print axioms packingLowerBound
#print axioms saturatedOptimal
#print axioms halfBudgetFromChargedWitness
#print axioms triangleTwoCutsHit
#print axioms triangleNoSingleton
#print axioms trianglePairsIntersect

end GlobalConflict
