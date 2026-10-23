import Exchange
namespace BinaryExchange
open RMAF VertexGeometry

/-- Construct an ORIGINAL source subtree whose selected leaves are exactly
one nonempty clade. Extra, unselected source leaves may lie in that subtree. -/
theorem cluster_subtree_witness (C : List Nat) (q : Nat → Bool) (s : Tree)
    (hc : Cluster (fun x => x ∈ C) q s)
    (ht : ∃ x, x ∈ leaves s ∧ x ∈ C ∧ q x = true) :
    ∃ w z, treeAt s w = some z ∧
      ∀ x, x ∈ C → x ∈ leaves s → (x ∈ leaves z ↔ q x = true) := by
  induction hc with
  | @allTrue s h =>
    exact ⟨[],s,by cases s <;> rfl,by intro x hx hxs; exact ⟨fun _ => h x hxs hx,fun _ => hxs⟩⟩
  | allFalse h =>
    obtain ⟨x,hxs,hx,hq⟩ := ht
    have hh := h x hxs hx
    simp [hq] at hh
  | @left l r hc hn ih =>
    have htl : ∃ x, x ∈ leaves l ∧ x ∈ C ∧ q x = true := by
      obtain ⟨x,hxs,hx,hq⟩ := ht
      rcases List.mem_append.1 hxs with hl | hr
      · exact ⟨x,hl,hx,hq⟩
      · have hh := hn x hr hx; simp [hq] at hh
    obtain ⟨w,z,hw,hz⟩ := ih htl
    refine ⟨false :: w,z,hw,?_⟩
    intro x hx hxs
    constructor
    · intro hxz
      exact (hz x hx (treeAt_mem l z w hw x hxz)).1 hxz
    · intro hq
      rcases List.mem_append.1 hxs with hl | hr
      · exact (hz x hx hl).2 hq
      · have hh := hn x hr hx; simp [hq] at hh
  | @right l r hn hc ih =>
    have htr : ∃ x, x ∈ leaves r ∧ x ∈ C ∧ q x = true := by
      obtain ⟨x,hxs,hx,hq⟩ := ht
      rcases List.mem_append.1 hxs with hl | hr
      · have hh := hn x hl hx; simp [hq] at hh
      · exact ⟨x,hr,hx,hq⟩
    obtain ⟨w,z,hw,hz⟩ := ih htr
    refine ⟨true :: w,z,hw,?_⟩
    intro x hx hxs
    constructor
    · intro hxz
      exact (hz x hx (treeAt_mem r z w hw x hxz)).1 hxz
    · intro hq
      rcases List.mem_append.1 hxs with hl | hr
      · have hh := hn x hl hx; simp [hq] at hh
      · exact (hz x hx hr).2 hq

/-- A mixed agreed FINAL C, never the unagreed original parent B, has a proper
literal source descendant edge realizing the two target colors on C. -/
theorem descendant_final_source_edge (s t u : Tree) (v : RMAF.Vertex) (C : List Nat)
    (hn : (leaves t).Nodup) (he : treeAt t v = some u)
    (ha : restrictionAgrees s t C = true) (hCl : Sub C (leaves s))
    (hm : mixed C ((leaves u).contains ·) = true) :
    ∃ w z, w ≠ [] ∧ treeAt s w = some z ∧
      ∀ x, x ∈ C → (x ∈ leaves z ↔ x ∈ leaves u) := by
  let q : Nat → Bool := fun x => (leaves u).contains x
  have hc := (descendant_agreed_split s t u v C hn he ha).1
  obtain ⟨⟨x,hx,hqx⟩,⟨y,hy,hqy⟩⟩ := (mixed_iff C q).1 hm
  obtain ⟨w,z,hw,hz⟩ := cluster_subtree_witness C q s hc ⟨x,hCl x hx,hx,hqx⟩
  have hne : w ≠ [] := by
    intro hwe
    subst w
    have hsz : s = z := Option.some.inj (by simpa [treeAt] using hw)
    have hh := (hz y hy (hCl y hy)).1 (by simpa [hsz] using hCl y hy)
    simp [hqy] at hh
  exact ⟨w,z,hne,hw,by intro a ha; simpa only [q,List.contains_iff_mem] using hz a ha (hCl a ha)⟩
end BinaryExchange
