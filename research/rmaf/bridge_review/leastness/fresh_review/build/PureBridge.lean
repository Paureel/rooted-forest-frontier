import Std

/-!
Pure-bridge exchange interface, not a graph-theoretic rMAF theorem.
Imports only Std. Every unproved realization obligation is a theorem argument
or structure field; none is installed as an axiom. See ../FORMAL.md.
-/
namespace PureBridge

abbrev Address := List Bool

/-- A nonempty rooted path-convex vertex family in the binary address tree.
No reference to the unformalized minimal-spanning-subtree construction. -/
structure RootedRegion where
  root : Address
  member : Address → Prop
  root_mem : member root
  below : ∀ v, member v → root.IsPrefix v
  convex : ∀ x y, root.IsPrefix x → x.IsPrefix y → member y → member x

/-- The deepest region's root lies in each intersecting region. The geometric
obligation is exactly that the input embeddings realize RootedRegion. -/
theorem deepest_root_in_neighbor (a b : RootedRegion)
    (hdepth : b.root.length ≤ a.root.length)
    (hoverlap : ∃ z, a.member z ∧ b.member z) : b.member a.root := by
  obtain ⟨z, haz, hbz⟩ := hoverlap
  have hap := a.below z haz
  have hbp := b.below z hbz
  have hba : b.root.IsPrefix a.root :=
    List.prefix_of_prefix_length_le hbp hap hdepth
  exact b.convex a.root z hba hap hbz

/-- Thus arbitrarily many neighbors form a clique through the selected root;
there is no two-neighbor restriction hidden in this statement. -/
theorem deepest_neighbors_intersect (a b c : RootedRegion)
    (hbdepth : b.root.length ≤ a.root.length)
    (hcdepth : c.root.length ≤ a.root.length)
    (hab : ∃ z, a.member z ∧ b.member z)
    (hac : ∃ z, a.member z ∧ c.member z) :
    ∃ z, b.member z ∧ c.member z := by
  exact ⟨a.root, deepest_root_in_neighbor a b hbdepth hab,
    deepest_root_in_neighbor a c hcdepth hac⟩

/-- Pairwise vertex disjointness makes the piece using any given vertex unique. -/
theorem at_most_one_occupant {I V : Type} (uses : I → V → Prop)
    (disjoint : ∀ i j, i ≠ j → ∀ v, uses i v → ¬ uses j v)
    (i j : I) (v : V) (hi : uses i v) (hj : uses j v) : i = j := by
  exact Classical.byContradiction (fun h => disjoint i j h v hi hj)

/-- Marks are predicates on vertices. The monotonicity theorem below does not
assume mark penalties are additive, submodular, or independent. -/
def Avoids {V : Type} (occupied marks : V → Prop) : Prop :=
  ∀ v, marks v → ¬ occupied v

theorem avoids_weaken {V : Type} (occupied j k : V → Prop)
    (hjk : ∀ v, j v → k v) (h : Avoids occupied k) : Avoids occupied j := by
  intro v hv
  exact h v (hjk v hv)

/-- Minimality is represented by an attained value and a lower bound. -/
def IsMinimum {X : Type} (valid : X → Prop) (cost : X → Nat) (m : Nat) : Prop :=
  (∃ x, valid x ∧ cost x = m) ∧ ∀ x, valid x → m ≤ cost x

/-- The exact abstract interface consumed by one elimination step.
`clearRest` must be realized by splitting at most one globally feasible piece,
with all old marks and all remaining pairwise disjointness preserved. -/
structure ExchangeSystem (A R : Type) where
  localValid : A → Prop
  restValid : R → Prop
  localCost : A → Nat
  restCost : R → Nat
  localAvoids : A → Prop
  restAvoids : R → Prop
  compatible : A → R → Prop
  freeLeft : ∀ a r, localValid a → restValid r → localAvoids a → compatible a r
  freeRight : ∀ a r, localValid a → restValid r → restAvoids r → compatible a r
  collision : ∀ a r, localValid a → restValid r → compatible a r →
    localAvoids a ∨ restAvoids r
  clearRest : ∀ r, restValid r → ∃ r', restValid r' ∧ restAvoids r' ∧
    restCost r' ≤ restCost r + 1

namespace ExchangeSystem
variable {A R : Type} (s : ExchangeSystem A R)

def feasible (ar : A × R) : Prop :=
  s.localValid ar.1 ∧ s.restValid ar.2 ∧ s.compatible ar.1 ar.2

def totalCost (ar : A × R) : Nat := s.localCost ar.1 + s.restCost ar.2

/-- In the zero-penalty branch, a minimum avoiding witness replaces the local
part of every feasible solution and keeps the remainder unchanged. -/
theorem free_replacement (a0 : A) (mu : Nat)
    (ha0 : s.localValid a0) (hc0 : s.localCost a0 = mu)
    (havoid : s.localAvoids a0)
    (hlower : ∀ a, s.localValid a → mu ≤ s.localCost a)
    (a : A) (r : R) (h : s.feasible (a,r)) :
    s.feasible (a0,r) ∧ s.totalCost (a0,r) ≤ s.totalCost (a,r) := by
  refine ⟨⟨ha0, h.2.1, s.freeLeft a0 r ha0 h.2.1 havoid⟩, ?_⟩
  have hh := hlower a h.1
  simp only [totalCost, hc0]
  omega

/-- Positive-penalty exchange. No assumption about sums of individual mark
penalties occurs: the sole repair bound concerns the entire remaining state. -/
theorem paid_replacement (a0 : A) (mu : Nat)
    (ha0 : s.localValid a0) (hc0 : s.localCost a0 = mu)
    (hlower : ∀ a, s.localValid a → mu ≤ s.localCost a)
    (hpaid : ∀ a, s.localValid a → s.localAvoids a → mu < s.localCost a)
    (a : A) (r : R) (h : s.feasible (a,r)) :
    ∃ r', s.feasible (a0,r') ∧ s.restAvoids r' ∧
      s.totalCost (a0,r') ≤ s.totalCost (a,r) := by
  have ha := h.1
  have hr := h.2.1
  rcases s.collision a r ha hr h.2.2 with hla | hra
  · obtain ⟨r', hr', har', hcr⟩ := s.clearRest r hr
    refine ⟨r', ⟨ha0, hr', s.freeRight a0 r' ha0 hr' har'⟩, har', ?_⟩
    have hgap := hpaid a ha hla
    simp only [totalCost, hc0]
    omega
  · refine ⟨r, ⟨ha0, hr, s.freeRight a0 r ha0 hr hra⟩, hra, ?_⟩
    have hlow := hlower a ha
    simp only [totalCost, hc0]
    omega

/-- Exact optimum identity for the positive-penalty elimination branch. -/
theorem paid_minimum (a0 : A) (mu nu : Nat)
    (ha0 : s.localValid a0) (hc0 : s.localCost a0 = mu)
    (hlower : ∀ a, s.localValid a → mu ≤ s.localCost a)
    (hpaid : ∀ a, s.localValid a → s.localAvoids a → mu < s.localCost a)
    (hrest : IsMinimum (fun r => s.restValid r ∧ s.restAvoids r) s.restCost nu) :
    IsMinimum s.feasible s.totalCost (mu + nu) := by
  obtain ⟨r0, hr0, hcr0⟩ := hrest.1
  constructor
  · refine ⟨(a0,r0), ⟨ha0, hr0.1, s.freeRight a0 r0 ha0 hr0.1 hr0.2⟩, ?_⟩
    simp [totalCost, hc0, hcr0]
  · intro ar h
    obtain ⟨r', hfeas, havoid, hcost⟩ :=
      s.paid_replacement a0 mu ha0 hc0 hlower hpaid ar.1 ar.2 h
    have hn := hrest.2 r' ⟨hfeas.2.1,havoid⟩
    simp only [totalCost, hc0] at hcost ⊢
    omega

/-- Exact optimum identity for the zero-penalty elimination branch. -/
theorem free_minimum (a0 : A) (mu nu : Nat)
    (ha0 : s.localValid a0) (hc0 : s.localCost a0 = mu)
    (havoid : s.localAvoids a0)
    (hlower : ∀ a, s.localValid a → mu ≤ s.localCost a)
    (hrest : IsMinimum s.restValid s.restCost nu) :
    IsMinimum s.feasible s.totalCost (mu + nu) := by
  obtain ⟨r0, hr0, hcr0⟩ := hrest.1
  constructor
  · refine ⟨(a0,r0), ⟨ha0, hr0, s.freeLeft a0 r0 ha0 hr0 havoid⟩, ?_⟩
    simp [totalCost, hc0, hcr0]
  · intro ar h
    have hl := hlower ar.1 h.1
    have hr := hrest.2 ar.2 h.2.1
    simp only [totalCost]
    omega
end ExchangeSystem

/-- The two-valued marked query conclusion, conditional on the geometric
one-cut repair estimate. Failure at budget mu implies exactly mu+1. -/
theorem one_cut_query_dichotomy (mu marked : Nat)
    (hmono : mu ≤ marked) (hrepair : marked ≤ mu + 1) :
    marked = mu ∨ marked = mu + 1 := by omega

/-- Role-swap parameter arithmetic, after partition equivalence, nonempty-region
counting, and the r-1 split bound have been proved in the graph model. -/
theorem role_swap_parameter (h r d : Nat) (hr : 1 ≤ r)
    (hregions : r ≤ h+1) (hupper : h ≤ d+(r-1)) :
    (h+1-r)+(r-1)=h ∧ h+1-r ≤ d := by omega

/-- If two formulations have exactly the same valid partitions, switching the
initial component count from one to r changes the optimum by r-1. The shared
partition equivalence is a visible hypothesis, not a proved graph fact. -/
theorem role_swap_minimum {P : Type} (valid : P → Prop) (pieces : P → Nat)
    (r h : Nat) (hr : 1 ≤ r) (hregions : ∀ p, valid p → r ≤ pieces p)
    (hmin : IsMinimum valid (fun p => pieces p - 1) h) :
    IsMinimum valid (fun p => pieces p-r) (h+1-r) := by
  obtain ⟨p0, hp0, hc0⟩ := hmin.1
  have hreg0 := hregions p0 hp0
  constructor
  · refine ⟨p0, hp0, ?_⟩
    dsimp only at hc0 ⊢
    omega
  · intro p hp
    have hlow := hmin.2 p hp
    have hreg := hregions p hp
    dsimp only at hlow ⊢
    omega

/-- The second query budget remains below the original unmarked local distance
when extra marks cannot decrease the number of nonempty regions. -/
theorem bounded_second_query (mu r r' d : Nat)
    (hr : 1 ≤ r) (hregions : r ≤ r') (hupper : mu ≤ d+(r-1)) :
    mu-(r'-1) ≤ d := by omega

/-- A comparison query with more regions than its piece budget is infeasible. -/
theorem negative_budget_impossible (mu r pieces : Nat)
    (hmany : mu+1 < r) (hregions : r ≤ pieces) : ¬ (pieces ≤ mu+1) := by omega

namespace Controls

/-- A finite two-state countermodel to omitting the one-unit repair condition.
`true` means occupying the shared vertex. Clearing the local side costs one;
clearing the remaining side costs two. -/
def badLocalCost (occupies : Bool) : Nat := if occupies then 0 else 1
def badRestCost (occupies : Bool) : Nat := if occupies then 0 else 2
def badCompatible (a r : Bool) : Prop := !(a && r) = true
def badCost (ar : Bool × Bool) : Nat := badLocalCost ar.1 + badRestCost ar.2

theorem bad_repair_optimum :
    IsMinimum (fun ar : Bool × Bool => badCompatible ar.1 ar.2) badCost 1 := by
  constructor
  · exact ⟨(false,true), by simp [badCompatible], by decide⟩
  · intro ar h
    rcases ar with ⟨a,r⟩
    cases a <;> cases r <;> simp_all [badCompatible, badCost, badLocalCost, badRestCost]

theorem bad_repair_forced_keeper :
    IsMinimum (fun r => badCompatible true r) (fun r => badCost (true,r)) 2 := by
  constructor
  · exact ⟨false, by simp [badCompatible], by decide⟩
  · intro r h
    cases r <;> simp_all [badCompatible, badCost, badLocalCost, badRestCost]

theorem one_unit_repair_rejected :
    ¬ (∃ r : Bool, r = false ∧ badRestCost r ≤ badRestCost true + 1) := by decide

end Controls

#print axioms deepest_root_in_neighbor
#print axioms deepest_neighbors_intersect
#print axioms at_most_one_occupant
#print axioms avoids_weaken
#print axioms ExchangeSystem.free_replacement
#print axioms ExchangeSystem.paid_replacement
#print axioms ExchangeSystem.paid_minimum
#print axioms ExchangeSystem.free_minimum
#print axioms one_cut_query_dichotomy
#print axioms role_swap_parameter
#print axioms role_swap_minimum
#print axioms bounded_second_query
#print axioms negative_budget_impossible
#print axioms Controls.bad_repair_optimum
#print axioms Controls.bad_repair_forced_keeper
#print axioms Controls.one_unit_repair_rejected

end PureBridge
