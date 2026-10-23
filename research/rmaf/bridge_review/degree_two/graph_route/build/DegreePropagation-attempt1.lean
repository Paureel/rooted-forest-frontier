import ActualEmbedding

/-! Graph-only degree propagation for the unchanged actual extractor.
ExactTwo is a semantic two-neighbor predicate on unsuppressed addresses.
No agreement refinement or cross-tree transport is asserted. -/
namespace DegreeTwoGraph
open RMAF BridgeReview ExecutableBridge LeastEmbedding

abbrev Members (s : ConnectedSupport) : Vertex → Prop :=
  fun x => x ∈ s.first :: s.rest

def HasTwo (P : Vertex → Prop) (v : Vertex) : Prop :=
  ∃ a b, a ≠ b ∧ P a ∧ Adj v a ∧ P b ∧ Adj v b

def ExactTwo (P : Vertex → Prop) (v : Vertex) : Prop :=
  ∃ a b, a ≠ b ∧ P a ∧ Adj v a ∧ P b ∧ Adj v b ∧
    ∀ x, P x → Adj v x → x = a ∨ x = b

theorem adj_ne {x y : Vertex} (h : Adj x y) : x ≠ y := by
  intro heq
  subst y
  rcases h with ⟨b,h⟩ | ⟨b,h⟩ <;>
    have hh := congrArg List.length h <;> simp at hh

theorem walk_neighbor {P : Vertex → Prop} {x y : Vertex}
    (w : Walk P x y) (hne : x ≠ y) : ∃ a, P a ∧ Adj x a := by
  induction w with
  | refl h => exact False.elim (hne rfl)
  | @step y z w he hz ih =>
    by_cases hxy : x = y
    · subst y; exact ⟨z,hz,he⟩
    · exact ih hxy

theorem walk_map_stutter {P Q : Vertex → Prop} {x y : Vertex}
    (f : Vertex → Vertex)
    (hmem : ∀ z, P z → Q (f z))
    (hedge : ∀ a b, P a → P b → Adj a b → f a = f b ∨ Adj (f a) (f b))
    (w : Walk P x y) : Walk Q (f x) (f y) := by
  induction w with
  | refl h => exact .refl (hmem _ h)
  | step w he hy ih =>
    rcases hedge _ _ w.finish hy he with h | h
    · simpa only [h] using ih
    · exact .step ih h (hmem _ hy)

theorem walk_erase_leaf {P : Vertex → Prop} {x y v a : Vertex}
    (ha : P a) (hav : a ≠ v)
    (hunique : ∀ z, P z → Adj v z → z = a)
    (w : Walk P x y) (hx : x ≠ v) (hy : y ≠ v) :
    Walk (fun z => P z ∧ z ≠ v) x y := by
  let f : Vertex → Vertex := fun z => if z = v then a else z
  have hm : ∀ z, P z → P (f z) ∧ f z ≠ v := by
    intro z hz
    by_cases h : z = v
    · simp [f,h,ha,hav]
    · simp [f,h,hz]
  have he : ∀ p q, P p → P q → Adj p q → f p = f q ∨ Adj (f p) (f q) := by
    intro p q hp hq hpq
    by_cases hpv : p = v
    · subst p
      have hqa := hunique q hq hpq
      have hqv : q ≠ v := (adj_ne hpq).symm
      exact Or.inl (by simp [f,hqa,hqv,hav])
    · by_cases hqv : q = v
      · subst q
        have hpa := hunique p hp (adj_symmetric hpq)
        exact Or.inl (by simp [f,hpv,hpa])
      · exact Or.inr (by simpa [f,hpv,hqv] using hpq)
  simpa [f,hx,hy] using walk_map_stutter f hm he w

theorem least_nonterminal_hasTwo (e : MinimalEmbedding) (v : Vertex)
    (hv : Members e.support v) (hnt : v ∉ e.terminals) :
    HasTwo (Members e.support) v := by
  classical
  obtain ⟨p,hp⟩ := List.exists_mem_of_ne_nil e.terminal_nonempty
  have hpP : Members e.support p := e.containsTerminals p hp
  have hpv : p ≠ v := by intro h; exact hnt (h ▸ hp)
  obtain ⟨a,ha,hea⟩ := walk_neighbor (e.support.connected v hv p hpP) hpv.symm
  have hav : a ≠ v := (adj_ne hea).symm
  by_contra htwo
  have huniq : ∀ z, Members e.support z → Adj v z → z = a := by
    intro z hz hez
    by_contra hza
    exact htwo ⟨a,z,hza.symm,ha,hea,hz,hez⟩
  let rest := (e.support.first :: e.support.rest).filter (fun z => z != v)
  have member_iff : ∀ z, z ∈ p :: rest ↔ Members e.support z ∧ z ≠ v := by
    intro z
    simp only [List.mem_cons, rest, List.mem_filter, bne_iff_ne, ne_eq]
    constructor
    · intro h
      rcases h with h | h
      · subst z; exact ⟨hpP,hpv⟩
      · exact h
    · intro h; exact Or.inr h
  let other : ConnectedSupport := {
    first := p
    rest := rest
    connected := by
      intro x hx y hy
      have hx' := (member_iff x).mp hx
      have hy' := (member_iff y).mp hy
      have w := walk_erase_leaf ha hav huniq
        (e.support.connected x hx'.1 y hy'.1) hx'.2 hy'.2
      exact walk_map id (by intro a b h; exact h)
        (fun z hz => (member_iff z).mpr hz) w
  }
  have hother : ∀ z, z ∈ other.first :: other.rest → Members e.support z ∧ z ≠ v := by
    intro z hz; exact (member_iff z).mp hz
  have hvother := e.minimal other
    (fun z hz => e.inAmbient z (hother z hz).1)
    (by
      intro z hz
      exact (member_iff z).mpr ⟨e.containsTerminals z hz, by intro h; exact hnt (h ▸ hz)⟩)
    v hv
  exact (hother v hvother).2 rfl

theorem exactTwo_of_subset {P Q : Vertex → Prop} {v : Vertex}
    (hsub : ∀ z, P z → Q z) (hlo : HasTwo P v) (hhi : ExactTwo Q v) :
    ExactTwo P v := by
  obtain ⟨a,b,hab,ha,hea,hb,heb⟩ := hlo
  obtain ⟨c,d,hcd,hc,hec,hd,hed,hall⟩ := hhi
  refine ⟨a,b,hab,ha,hea,hb,heb,?_⟩
  intro z hz hez
  have ha' := hall a (hsub a ha) hea
  have hb' := hall b (hsub b hb) heb
  have hz' := hall z (hsub z hz) hez
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact False.elim (hab rfl)
  · exact hz'
  · exact hz'.elim Or.inr Or.inl
  · exact False.elim (hab rfl)

theorem terminals_mono (B S : List Nat) (t : Tree)
    (hsub : ∀ x, x ∈ B → x ∈ S) :
    ∀ v, v ∈ terminals B t → v ∈ terminals S t := by
  intro v hv
  obtain ⟨x,hocc,hx⟩ := mem_terminals_iff.mp hv
  exact mem_terminals_iff.mpr ⟨x,hocc,hsub x hx⟩

theorem actual_support_mono (B S : List Nat) (t : Tree)
    (hsub : ∀ x, x ∈ B → x ∈ S) :
    ∀ v, v ∈ minimalVertices B t → v ∈ minimalVertices S t := by
  intro v hv
  obtain ⟨p,hp,_⟩ := minimal_terminal_descendant B t v hv
  have hpS := terminals_in_minimal S t p (terminals_mono B S t hsub p hp)
  have hne : minimalVertices S t ≠ [] := by intro h; simp [h] at hpS
  have h := minimal_least B t (extractedSupport S t hne)
    (by intro q hq; simpa only [extractedSupport_exact] using
      terminals_in_minimal S t q (terminals_mono B S t hsub q hq)) v hv
  simpa only [extractedSupport_exact] using h

theorem actual_nonterminal_hasTwo (B : List Nat) (t : Tree) (v : Vertex)
    (hv : v ∈ minimalVertices B t) (hnt : v ∉ terminals B t) :
    HasTwo (fun z => z ∈ minimalVertices B t) v := by
  obtain ⟨p,hp,_⟩ := minimal_terminal_descendant B t v hv
  obtain ⟨x,hocc,hxB⟩ := mem_terminals_iff.mp hp
  have hxt : x ∈ leaves t := leafOccurrence_mem_leaves hocc
  have h := least_nonterminal_hasTwo (embedding B t x hxt hxB) v
    (by simpa only [Members,embedding_support_exact] using hv)
    (by simpa only [embedding_terminals_exact] using hnt)
  simpa only [HasTwo, Members, embedding_support_exact] using h

theorem actual_degree_propagation (B S : List Nat) (t : Tree) (v : Vertex)
    (hsub : ∀ x, x ∈ B → x ∈ S)
    (hv : v ∈ minimalVertices B t) (hnt : v ∉ terminals B t)
    (hdegree : ExactTwo (fun z => z ∈ minimalVertices S t) v) :
    ExactTwo (fun z => z ∈ minimalVertices B t) v := by
  exact exactTwo_of_subset (actual_support_mono B S t hsub)
    (actual_nonterminal_hasTwo B t v hv hnt) hdegree

#print axioms least_nonterminal_hasTwo
#print axioms actual_support_mono
#print axioms actual_nonterminal_hasTwo
#print axioms actual_degree_propagation
end DegreeTwoGraph
