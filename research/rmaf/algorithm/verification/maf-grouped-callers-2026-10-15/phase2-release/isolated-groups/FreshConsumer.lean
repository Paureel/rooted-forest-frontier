import FreshReadout
namespace NonauthorGroupedConsumer
open RMAF RestrictionBridge ForestState ForestGroups

def a : Tree := .node (.leaf 0) (.node (.leaf 1) (.leaf 2))
def b1 : Tree := .node (.leaf 3) (.leaf 5)
def b2 : Tree := .node (.leaf 4) (.leaf 6)
def T : Tree := .node (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
  (.node (.node (.leaf 3) (.leaf 4)) (.node (.leaf 5) (.leaf 6)))) (.leaf 7)
def ss : List Tree := [a,b1,b2,.leaf 7]
def A : List Nat := [0,1,2]
def B : List Nat := [3,4,5,6]
def C : List Nat := [7]
def FA : List (List Nat) := [[0,1],[2]]
def FB : List (List Nat) := [[3],[4],[5],[6]]
def FC : List (List Nat) := [[7]]

theorem pieces_clear : PriorityClear (some T) a [b1,b2] [.leaf 7] := by
  intro t ht
  have eq : T=t := Option.some.inj ht
  subst t
  simp only [List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  repeat' constructor
  all_goals apply (clear_iff _ _).1
  all_goals decide

/-- Actual root fixture, arbitrary valid residual FOREST on the actual two B
source pieces. No within-B clearance or whole-B replacement is supplied. -/
theorem any_actual_B (F : List (List Nat))
    (hB : agrees (localTarget (some T) B) [b1,b2] F=true) :
    agrees (some T) ss (FA++F++FC)=true ∧
    additionalCost ss (FA++F++FC)=1+additionalCost [b1,b2] F := by
  exact retained_A_one_plus_Bforest (some T) a [b1,b2] [.leaf 7] A B C FA F FC
    (by decide) (by decide) (by decide) (by decide) (by decide) pieces_clear
    (by decide) (by decide) hB (by decide) (by decide)

theorem literal_root :
    disjointVertices (minimalVertices (leaves b1) T) (minimalVertices (leaves b2) T)=false ∧
    agrees (some T) ss (FA++FB++FC)=true ∧ additionalCost ss (FA++FB++FC)=3 := by
  have h := any_actual_B FB (by decide)
  exact ⟨by decide,h.1,by simpa [FB,additionalCost] using h.2⟩

theorem supplied_B_is_not_required_minimum :
    agrees (localTarget (some T) B) [b1,b2] [[3],[5],[4,6]]=true ∧
    additionalCost [b1,b2] [[3],[5],[4,6]]=1 ∧ additionalCost [b1,b2] FB=2 := by decide

/-- Child-specific feasibility contract remains explicit at its exact target,
source list and q-1. This theorem does not establish that recursive contract. -/
theorem conditional_exact_child
    (solve : Option Tree → List Tree → Nat → Option (List (List Nat)))
    (q : Nat) (positive : 0<q)
    (IH : ResidualSolverContract solve (localTarget (some T) B) [b1,b2] (q-1))
    (F : List (List Nat)) (query : solve (localTarget (some T) B) [b1,b2] (q-1)=some F) :
    agrees (some T) ss (FA++F++FC)=true ∧ additionalCost ss (FA++F++FC)≤q := by
  exact residual_query_lift solve (some T) a [b1,b2] [.leaf 7] A B C FA F FC q positive IH
    (by decide) (by decide) (by decide) (by decide) (by decide) pieces_clear
    (by decide) (by decide) (by decide) (by decide) query
end NonauthorGroupedConsumer
