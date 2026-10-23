import ExecutableConnectivity
open RMAF BridgeReview ExecutableBridge
namespace FreshExecutableReview

-- Exact Walk predicate and adjacency imported from GraphRegion.
theorem exact_walk (selected : List Nat) (t : Tree)
    (u v : Vertex) (hu : u ∈ minimalVertices selected t)
    (hv : v ∈ minimalVertices selected t) :
    BridgeReview.Walk (fun x => x ∈ RMAF.minimalVertices selected t) u v :=
  minimalVertices_connected selected t u hu v hv

-- Actual label occurrence supplies nonemptiness without geometric premises.
noncomputable def region_from_occurrence (selected : List Nat) (t : Tree) (x : Nat)
    (hx : x ∈ leaves t) (hs : x ∈ selected) : PureBridge.RootedRegion :=
  extractedRegion selected t (minimalVertices_nonempty_of_leaf selected t x hx hs)

theorem occurrence_exact (selected : List Nat) (t : Tree) (x : Nat)
    (hx : x ∈ leaves t) (hs : x ∈ selected) (v : Vertex) :
    (region_from_occurrence selected t x hx hs).member v ↔ v ∈ minimalVertices selected t :=
  extractedRegion_exact selected t _ v

-- A direct use of the original consumer, independently restated.
theorem through_original_consumer (sa sb : List Nat) (ta tb : Tree)
    (ha : minimalVertices sa ta ≠ []) (hb : minimalVertices sb tb ≠ [])
    (hdepth : (extractedSupport sb tb hb).root.length ≤ (extractedSupport sa ta ha).root.length)
    (hoverlap : ∃ z, z ∈ minimalVertices sa ta ∧ z ∈ minimalVertices sb tb) :
    (extractedSupport sa ta ha).root ∈ minimalVertices sb tb := by
  have shared : ∃ z, (extractedRegion sa ta ha).member z ∧ (extractedRegion sb tb hb).member z := by
    obtain ⟨z, haz, hbz⟩ := hoverlap
    exact ⟨z, (extractedRegion_exact sa ta ha z).mpr haz, (extractedRegion_exact sb tb hb z).mpr hbz⟩
  have h := PureBridge.deepest_root_in_neighbor
    (extractedRegion sa ta ha) (extractedRegion sb tb hb) hdepth shared
  exact (extractedRegion_exact sb tb hb _).mp h

#print axioms exact_walk
#print axioms region_from_occurrence
#print axioms occurrence_exact
#print axioms through_original_consumer
#check @minimalVertices_connected
#check @minimalVertices_nonempty_of_leaf
#check @extractedSupport
#check @extractedSupport_exact
#check @extractedRegion_exact
#check @deepest_extracted_root_in_neighbor
end FreshExecutableReview
