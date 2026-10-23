import ExtractorLeastness

/-! Actual MinimalEmbedding construction. The only input witness says that a
selected label occurs in the given tree. Every geometric structure field is
derived from the unchanged extractor and the actual occurrence definitions. -/
namespace LeastEmbedding
open RMAF BridgeReview ExecutableBridge

def embedding (selected : List Nat) (t : Tree) (x : Nat)
    (hx : x ∈ leaves t) (hs : x ∈ selected) : MinimalEmbedding where
  ambient := vertices t
  terminals := terminals selected t
  terminal_nonempty := terminal_nonempty hx hs
  support := extractedSupport selected t (minimalVertices_nonempty_of_leaf selected t x hx hs)
  inAmbient := by
    intro v hv
    exact minimal_in_vertices selected t v (by simpa only [extractedSupport_exact] using hv)
  containsTerminals := by
    intro v hv
    simpa only [extractedSupport_exact] using terminals_in_minimal selected t v hv
  minimal := by
    intro other _ hterm v hv
    exact minimal_least selected t other hterm v (by simpa only [extractedSupport_exact] using hv)

theorem embedding_ambient_exact (selected : List Nat) (t : Tree) (x : Nat)
    (hx : x ∈ leaves t) (hs : x ∈ selected) :
    (embedding selected t x hx hs).ambient = vertices t := rfl

theorem embedding_terminals_exact (selected : List Nat) (t : Tree) (x : Nat)
    (hx : x ∈ leaves t) (hs : x ∈ selected) :
    (embedding selected t x hx hs).terminals = terminals selected t := rfl

theorem embedding_support_exact (selected : List Nat) (t : Tree) (x : Nat)
    (hx : x ∈ leaves t) (hs : x ∈ selected) :
    (embedding selected t x hx hs).support.first :: (embedding selected t x hx hs).support.rest =
      minimalVertices selected t := extractedSupport_exact selected t _

theorem embedding_ambient_iff (selected : List Nat) (t : Tree) (x : Nat)
    (hx : x ∈ leaves t) (hs : x ∈ selected) (v : Vertex) :
    v ∈ (embedding selected t x hx hs).ambient ↔ ValidVertex t v := mem_vertices_iff

theorem embedding_terminals_iff (selected : List Nat) (t : Tree) (x : Nat)
    (hx : x ∈ leaves t) (hs : x ∈ selected) (v : Vertex) :
    v ∈ (embedding selected t x hx hs).terminals ↔
      ∃ y, LeafOccurrence t v y ∧ y ∈ selected := mem_terminals_iff

theorem embedding_region_exact (selected : List Nat) (t : Tree) (x : Nat)
    (hx : x ∈ leaves t) (hs : x ∈ selected) (v : Vertex) :
    (embedding selected t x hx hs).region.member v ↔ v ∈ minimalVertices selected t := by
  change v ∈ (embedding selected t x hx hs).support.first ::
    (embedding selected t x hx hs).support.rest ↔ _
  rw [embedding_support_exact]

/-- The original MinimalEmbedding consumer is instantiated with the actual
extractor. Equal addresses in distinct input trees are only coordinates. -/
theorem embedding_consumer (sa sb : List Nat) (ta tb : Tree) (xa xb : Nat)
    (hxa : xa ∈ leaves ta) (hsa : xa ∈ sa) (hxb : xb ∈ leaves tb) (hsb : xb ∈ sb)
    (hdepth : (embedding sb tb xb hxb hsb).support.root.length ≤
      (embedding sa ta xa hxa hsa).support.root.length)
    (hoverlap : ∃ v, v ∈ minimalVertices sa ta ∧ v ∈ minimalVertices sb tb) :
    (embedding sa ta xa hxa hsa).support.root ∈ minimalVertices sb tb := by
  have h := MinimalEmbedding.deepest_root_in_neighbor
    (embedding sa ta xa hxa hsa) (embedding sb tb xb hxb hsb) hdepth
    (by simpa only [embedding_support_exact] using hoverlap)
  simpa only [embedding_support_exact] using h

#print axioms embedding
#print axioms embedding_ambient_exact
#print axioms embedding_terminals_exact
#print axioms embedding_support_exact
#print axioms embedding_ambient_iff
#print axioms embedding_terminals_iff
#print axioms embedding_region_exact
#print axioms embedding_consumer
end LeastEmbedding
