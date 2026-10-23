import Optimality01

namespace Universal233.DepthOne
open RMAF CoreGraph CutRealization RestrictionBridge Integration

def sourceCuts : Option Vertex → List Vertex
  | none => []
  | some p => [p]

def components (S : Tree) : Option Vertex → List (Vertex × List Nat)
  | none => [([],leaves S)]
  | some p => [(p,subtreeLabels S p),([],complement S p)]

theorem candidate_history (S : Tree) (c : Option Vertex) (hc : c ∈ candidates S) :
    CutHistory S (sourceCuts c) := by
  cases c with
  | none => exact .nil
  | some p =>
    have hp : p ∈ edges S := by simpa [candidates] using hc
    obtain ⟨hv,hn⟩ := (mem_edges S p).1 hp
    exact .cons p .nil hv hn (live_nil p)

theorem labels_of_subset (S : Tree) (L : List Nat) (h : L ⊆ leaves S) : LabelsValid S L := by
  intro x hx
  exact leaf_exists (h hx)

theorem leaf_subtree_iff (S : Tree) (p a : Vertex) (x : Nat)
    (hn : (leaves S).Nodup) (ha : LeafAt S a x) :
    x ∈ subtreeLabels S p ↔ Pre p a := by
  constructor
  · intro hx
    obtain ⟨b,hb,hpb⟩ := (subtreeLabels_mem S p x).1 hx
    have he := leaf_unique hn hb ha
    simpa only [he] using hpb
  · intro hp
    exact (subtreeLabels_mem S p x).2 ⟨a,ha,hp⟩

theorem candidate_components (S : Tree) (c : Option Vertex)
    (hn : (leaves S).Nodup) (hc : c ∈ candidates S)
    (hp : partitionCheck (leaves S) (forest S c) = true) :
    ∀ r L, (r,L) ∈ components S c → ComponentLabels S (sourceCuts c) r L := by
  have hh := candidate_history S c hc
  cases c with
  | none =>
    intro r L hm
    have he : (r,L) = ([],leaves S) := by simpa [components] using hm
    cases he
    apply component_of_region hh (Or.inl rfl) (labels_of_subset S _ (fun _ h => h)) (CutRealization.leaves_nonempty S)
    intro a x ha
    have hx : x ∈ leaves S := leafAt_label S a x ha
    simp [hx,Region,sourceCuts]
  | some p =>
    have hpe : p ∈ edges S := by simpa [candidates] using hc
    obtain ⟨hv,hnr⟩ := (mem_edges S p).1 hpe
    have hnA := checked_nonempty (leaves S) (forest S (some p)) hp (subtreeLabels S p) (by simp [forest])
    have hnB := checked_nonempty (leaves S) (forest S (some p)) hp (complement S p) (by simp [forest])
    intro r L hm
    simp only [components,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hm
    rcases hm with ⟨hr,hL⟩ | ⟨hr,hL⟩
    · rw [hr,hL]
      apply component_of_region hh (Or.inr (by simp [sourceCuts]))
        (labels_of_subset S _ (subtreeLabels_subset S p)) hnA
      intro a x ha
      rw [leaf_subtree_iff S p a x hn ha]
      change Pre p a ↔ Region [p] p a
      constructor
      · intro h; refine ⟨h,?_⟩
        intro q hq hqa
        have he : q = p := by simpa using hq
        subst q
        exact List.prefix_rfl
      · exact And.left
    · rw [hr,hL]
      apply component_of_region hh (Or.inl rfl)
        (labels_of_subset S _ (fun _ hx => (List.mem_filter.1 hx).1)) hnB
      intro a x ha
      have hx : x ∈ leaves S := leafAt_label S a x ha
      have hreg := region_root [p] a (by
        intro q hq
        have he : q = p := by simpa using hq
        simpa [he] using hnr)
      simp only [complement,List.mem_filter,hx,true_and,Bool.not_eq_true',Bool.eq_false_iff]
      change ((subtreeLabels S p).contains x ≠ true) ↔ Region [p] [] a
      rw [hreg,live_cons]
      simp only [live_nil,and_true]
      exact not_congr (List.contains_iff_mem.trans (leaf_subtree_iff S p a x hn ha))

/-- Every found forest is the literal partition of every leaf-bearing component
after its zero or one ORIGINAL source edge is removed. Suppressed vertices are
included in the residual graph and all actual source vertices are covered. -/
theorem literal_realization (S : Tree) (c : Option Vertex)
    (hn : (leaves S).Nodup) (hc : c ∈ candidates S)
    (hp : partitionCheck (leaves S) (forest S c) = true) :
    RealizedOutput S ⟨forest S c,sourceCuts c⟩ := by
  have hh := candidate_history S c hc
  have hcomp := candidate_components S c hn hc hp
  have roots : (components S c).map Prod.fst = sourceCuts c ++ [[]] := by cases c <;> simp [components,sourceCuts]
  have blocks : (components S c).map Prod.snd = forest S c := by cases c <;> simp [components,forest]
  refine ⟨hh.good,hh.actual,components S c,roots,blocks,hcomp,roots ▸ roots_nodup hh.good,?_,?_,?_,?_⟩
  · intro v hv
    obtain ⟨r,hr,hw⟩ := hh.all_components v hv
    refine ⟨r,?_,hw⟩
    rw [roots]
    simpa [or_comm] using hr
  · intro r hr s hs
    rw [roots] at hr hs
    have hrr : r = [] ∨ r ∈ sourceCuts c := by simpa [or_comm] using hr
    have hss : s = [] ∨ s ∈ sourceCuts c := by simpa [or_comm] using hs
    exact hh.rooted_components hrr hss
  · intro v hv
    obtain ⟨r,hr,hw⟩ := hh.all_components v hv
    have hrmem : r ∈ (components S c).map Prod.fst := by rw [roots]; simpa [or_comm] using hr
    obtain ⟨pair,hpair,he⟩ := List.mem_map.1 hrmem
    have hepair : pair = (r,pair.2) := by cases pair; simp_all
    have hcl := hcomp r pair.2 (hepair ▸ hpair)
    obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil pair.2 hcl.nonempty
    obtain ⟨a,ha⟩ := hcl.labelsValid x hx
    exact ⟨a,x,ha,hw.reverse.trans ((hcl.exact a x ha).1 hx)⟩
  · cases c <;> simp [forest,sourceCuts]

theorem found_original_minimum (T S : Tree) (c : Option Vertex)
    (h : pretest01 T S = .found c) :
    agreement T S (forest S c) = true ∧
    RealizedOutput S ⟨forest S c,sourceCuts c⟩ ∧
    (sourceCuts c).length = cutCost c ∧ cutCost c ≤ 1 ∧
    ∀ F, agreement T S F = true → cutCost c ≤ F.length - 1 := by
  obtain ⟨hp,hc,ha,hmin⟩ := found_spec T S c h
  have hh := ha
  simp only [agreement,Bool.and_eq_true] at hh
  exact ⟨ha,literal_realization S c ((proper_iff T S).1 hp).2.1 hc hh.1.1.1.2,
    by cases c <;> simp [sourceCuts,cutCost],cutCost_le_one c,(found_globally_minimum T S c h).2.2⟩

end Universal233.DepthOne
