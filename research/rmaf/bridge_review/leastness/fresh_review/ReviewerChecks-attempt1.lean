import ActualEmbedding

namespace FreshLeastnessReview
open RMAF BridgeReview ExecutableBridge LeastEmbedding

def quartet : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def repeated : Tree := .node (.leaf 0) (.leaf 0)
def deep : Tree := .node (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 3)) (.leaf 4)

theorem crossing : minimalVertices [0,2] quartet =
    [[],[false],[false,false],[true],[true,false]] := by decide
theorem singleton : minimalVertices [0] quartet = [[false,false]] := by decide
theorem siblings : minimalVertices [0,1] quartet = [[false],[false,false],[false,true]] := by decide
theorem emptySelection : minimalVertices [] quartet = [] := by decide
theorem absentSelection : minimalVertices [9] quartet = [] := by decide
theorem rootLeaf : minimalVertices [0] (.leaf 0) = [[]] := by decide
theorem rootAbsent : minimalVertices [9] (.leaf 0) = [] := by decide
theorem duplicateLabels : minimalVertices [0] repeated = [[],[false],[true]] := by decide
theorem duplicateSelection : minimalVertices [0,0] quartet = [[false,false]] := by decide
theorem duplicateBoth : minimalVertices [0,0] repeated = [[],[false],[true]] := by decide
theorem deepSuppression : minimalVertices [0,1] deep =
    [[false,false,false],[false,false,false,false],[false,false,false,true]] := by decide

theorem duplicateOccurrences : terminals [0,0] repeated = [[false],[true]] := by decide
theorem duplicateSelectionNull : terminals [0,0] quartet = terminals [0] quartet := by decide

theorem repeatedLabelRefutesInjectivity :
    ¬ (∀ v w, LeafOccurrence repeated v 0 → LeafOccurrence repeated w 0 → v = w) := by
  intro h
  have he := h [false] [true] (.left (.leaf 0)) (.right (.leaf 0))
  cases he

theorem labelFunctionality (t : Tree) (v : Vertex) (x y : Nat)
    (hx : LeafOccurrence t v x) (hy : LeafOccurrence t v y) : x = y := hx.label_unique hy

theorem instanceAddresses (i : Instance) (x : Nat) (hx : x < i.n) :
    (∃ v, LeafOccurrence i.left v x ∧ ∀ w, LeafOccurrence i.left w x → w = v) ∧
    (∃ v, LeafOccurrence i.right v x ∧ ∀ w, LeafOccurrence i.right w x → w = v) :=
  ⟨instance_left_unique_occurrence i hx, instance_right_unique_occurrence i hx⟩

theorem exactObject (selected : List Nat) (t : Tree)
    (h : ∃ x, x ∈ leaves t ∧ x ∈ selected) :
    ∃ e : MinimalEmbedding,
      e.ambient = vertices t ∧ e.terminals = terminals selected t ∧
      e.support.first :: e.support.rest = minimalVertices selected t ∧
      (∀ v, v ∈ e.ambient ↔ ValidVertex t v) ∧
      (∀ v, v ∈ e.terminals ↔ ∃ y, LeafOccurrence t v y ∧ y ∈ selected) ∧
      (∀ v, e.region.member v ↔ v ∈ minimalVertices selected t) := by
  obtain ⟨x,hx,hs⟩ := h
  exact ⟨embedding selected t x hx hs, rfl, rfl,
    embedding_support_exact selected t x hx hs,
    embedding_ambient_iff selected t x hx hs,
    embedding_terminals_iff selected t x hx hs,
    embedding_region_exact selected t x hx hs⟩

theorem useAllFields (selected : List Nat) (t : Tree) (x : Nat)
    (hx : x ∈ leaves t) (hs : x ∈ selected) :
    terminals selected t ≠ [] ∧ minimalVertices selected t ≠ [] ∧
    Connected (minimalVertices selected t) ∧
    (∀ v, v ∈ minimalVertices selected t → ValidVertex t v) ∧
    (∀ v y, LeafOccurrence t v y → y ∈ selected → v ∈ minimalVertices selected t) ∧
    (∀ other : ConnectedSupport,
      (∀ v, v ∈ other.first :: other.rest → ValidVertex t v) →
      (∀ v y, LeafOccurrence t v y → y ∈ selected → v ∈ other.first :: other.rest) →
      ∀ v, v ∈ minimalVertices selected t → v ∈ other.first :: other.rest) := by
  let e := embedding selected t x hx hs
  have he : e.support.first :: e.support.rest = minimalVertices selected t :=
    embedding_support_exact selected t x hx hs
  refine ⟨e.terminal_nonempty, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← he]; exact List.cons_ne_nil _ _
  · simpa only [← he] using e.support.connected
  · intro v hv
    exact mem_vertices_iff.mp (e.inAmbient v (by simpa only [he] using hv))
  · intro v y hv hy
    have ht : v ∈ e.terminals := mem_terminals_iff.mpr ⟨y,hv,hy⟩
    simpa only [he] using e.containsTerminals v ht
  · intro other hamb hterm v hv
    apply e.minimal other (fun w hw => mem_vertices_iff.mpr (hamb w hw))
    · intro w hw
      obtain ⟨y,hy,hs'⟩ := mem_terminals_iff.mp hw
      exact hterm w y hy hs'
    · simpa only [he] using hv

theorem originalConsumer (sa sb : List Nat) (ta tb : Tree) (xa xb : Nat)
    (hxa : xa ∈ leaves ta) (hsa : xa ∈ sa) (hxb : xb ∈ leaves tb) (hsb : xb ∈ sb)
    (hd : (embedding sb tb xb hxb hsb).support.root.length ≤
      (embedding sa ta xa hxa hsa).support.root.length)
    (ho : ∃ v, v ∈ minimalVertices sa ta ∧ v ∈ minimalVertices sb tb) :
    (embedding sa ta xa hxa hsa).support.root ∈ minimalVertices sb tb := by
  have actual := MinimalEmbedding.deepest_root_in_neighbor
    (embedding sa ta xa hxa hsa) (embedding sb tb xb hxb hsb) hd
    (by simpa only [embedding_support_exact] using ho)
  simpa only [embedding_support_exact] using actual

def extraRootSupport : ConnectedSupport where
  first := []
  rest := [[false],[false,false],[false,true]]
  connected := by
    simpa [quartet, rootedSpan, prependSide] using rootedSpan_connected [0,1] quartet

def siblingEmbedding : MinimalEmbedding := embedding [0,1] quartet 0 (by decide) (by decide)

theorem extraRootAmbient : ∀ v, v ∈ extraRootSupport.first :: extraRootSupport.rest →
    v ∈ vertices quartet := by
  intro v hv
  simp only [extraRootSupport, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> decide

theorem extraRootContains : ∀ v, v ∈ terminals [0,1] quartet →
    v ∈ extraRootSupport.first :: extraRootSupport.rest := by
  intro v hv
  have ht : terminals [0,1] quartet = [[false,false],[false,true]] := by decide
  rw [ht] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> decide

theorem extraRootNotLeast : ¬ (∀ other : ConnectedSupport,
    (∀ v, v ∈ other.first :: other.rest → v ∈ vertices quartet) →
    (∀ v, v ∈ terminals [0,1] quartet → v ∈ other.first :: other.rest) →
    ∀ v, v ∈ extraRootSupport.first :: extraRootSupport.rest → v ∈ other.first :: other.rest) := by
  intro h
  have hc := h siblingEmbedding.support siblingEmbedding.inAmbient
    siblingEmbedding.containsTerminals [] (by decide)
  have he : siblingEmbedding.support.first :: siblingEmbedding.support.rest =
      minimalVertices [0,1] quartet := embedding_support_exact [0,1] quartet 0 (by decide) (by decide)
  rw [he, siblings] at hc
  simp at hc

def missingPath : List Vertex := [[],[false,false],[true],[true,false]]
theorem pathDeletionDisconnects : ¬ Connected missingPath := by
  intro h
  have walk := h [] (by decide) [false,false] (by decide)
  have hp := walk_ancestor_between walk [false] List.nil_prefix (by decide)
  simp [missingPath] at hp

theorem invalidAmbient : ¬ ValidVertex quartet [false,false,false] := by
  rw [← mem_vertices_iff]
  decide

theorem missingTerminal : ¬ (∀ v, v ∈ terminals [0,1] quartet → v ∈ ([[false],[false,false]] : List Vertex)) := by
  intro h
  have hm := h [false,true] (by decide)
  simp at hm

#print axioms exactObject
#print axioms useAllFields
#print axioms originalConsumer
#print axioms instanceAddresses
#print axioms extraRootNotLeast
#print axioms pathDeletionDisconnects
#print axioms repeatedLabelRefutesInjectivity
end FreshLeastnessReview
