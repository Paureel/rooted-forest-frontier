import RMAF

/-! Concrete degree-two mark interaction in the existing executable RMAF model.
Shared semantic lineage: imports RMAF's restrictions and minimal vertices.
Graph-theoretic equivalence of that model remains open. -/
namespace PureBridgeMarks
open RMAF

def target : Tree := .node (.node (.leaf 0) (.leaf 3))
  (.node (.leaf 1) (.node (.leaf 2) (.leaf 4)))
def source : Tree := .node (.node (.leaf 0) (.leaf 2)) (.leaf 1)
def markV : Vertex := [false]
def markW : Vertex := [true,true]

def neighbors (v : Vertex) : List Vertex :=
  if v.isEmpty then [[false],[true]]
  else [v.dropLast, v ++ [false], v ++ [true]]

def degreeInSpan (v : Vertex) : Nat :=
  ((neighbors v).filter fun w => (minimalVertices [0,1,2] target).contains w).length

def localValid (bs : List (List Nat)) : Bool :=
  partitionCheck [0,1,2] bs && bs.all (restrictionAgrees source target) &&
  pairwiseEmbeddings source bs && pairwiseEmbeddings target bs

def avoids (marks : List Vertex) (bs : List (List Nat)) : Bool :=
  bs.all fun b => disjointVertices (minimalVertices b target) marks

def valid (marks : List Vertex) (a : List Nat) : Bool :=
  localValid (blocks a) && avoids marks (blocks a)

def cutCost (a : List Nat) : Nat := (blocks a).length - 1

def solve (marks : List Vertex) : Option (List Nat) :=
  best cutCost (valid marks) (assignments 3 3)

def optimum (marks : List Vertex) : Option Nat := (solve marks).map cutCost

theorem proper_labels : (leaves source).Perm [0,1,2] ∧
    (leaves target).Perm [0,1,2,3,4] := by decide

theorem vertex_marks_have_degree_two : degreeInSpan markV = 2 ∧ degreeInSpan markW = 2 := by decide

theorem marks_are_unlabelled :
    (minimalVertices [0] target).contains markV = false ∧
    (minimalVertices [0] target).contains markW = false ∧
    (minimalVertices [1] target).contains markV = false ∧
    (minimalVertices [1] target).contains markW = false ∧
    (minimalVertices [2] target).contains markV = false ∧
    (minimalVertices [2] target).contains markW = false ∧
    (minimalVertices [3] target).contains markV = false ∧
    (minimalVertices [3] target).contains markW = false ∧
    (minimalVertices [4] target).contains markV = false ∧
    (minimalVertices [4] target).contains markW = false := by decide

theorem exact_four_optima :
    optimum [] = some 1 ∧ optimum [markV] = some 1 ∧
    optimum [markW] = some 1 ∧ optimum [markV,markW] = some 2 := by decide

theorem joint_mark_witness :
    valid [markV,markW] [0,1,2] = true ∧ cutCost [0,1,2] = 2 := by decide

/-- General lower bound for each fixed finite instance, using enumeration
completeness rather than merely stating a value returned by evaluation. -/
theorem every_feasible_at_least (marks : List Vertex) (m : Nat)
    (hopt : optimum marks = some m) (a : List Nat) (hlen : a.length = 3)
    (hbound : ∀ x ∈ a, x < 3) (hvalid : valid marks a = true) : m ≤ cutCost a := by
  cases hs : solve marks with
  | none => simp [optimum,hs] at hopt
  | some winner =>
    have hm : cutCost winner = m := by simpa [optimum,hs] using hopt
    have hbest := best_spec cutCost (valid marks) (assignments 3 3) winner hs
    have hle := hbest.2.2 a (assignments_complete 3 3 a hlen hbound) hvalid
    omega

theorem every_joint_mark_forest_costs_two (a : List Nat) (hlen : a.length = 3)
    (hbound : ∀ x ∈ a, x < 3) (hvalid : valid [markV,markW] a = true) :
    2 ≤ cutCost a := by
  exact every_feasible_at_least [markV,markW] 2 exact_four_optima.2.2.2 a hlen hbound hvalid

theorem separate_zero_penalties_do_not_compose :
    optimum [] = some 1 ∧ optimum [markV] = some 1 ∧ optimum [markW] = some 1 ∧
    ¬ (∃ a : List Nat, a.length = 3 ∧ (∀ x ∈ a, x < 3) ∧
      valid [markV,markW] a = true ∧ cutCost a ≤ 1) := by
  refine ⟨exact_four_optima.1, exact_four_optima.2.1, exact_four_optima.2.2.1, ?_⟩
  intro h
  obtain ⟨a,hlen,hbound,hvalid,hcost⟩ := h
  have lower := every_joint_mark_forest_costs_two a hlen hbound hvalid
  omega

#print axioms proper_labels
#print axioms vertex_marks_have_degree_two
#print axioms marks_are_unlabelled
#print axioms exact_four_optima
#print axioms joint_mark_witness
#print axioms every_feasible_at_least
#print axioms every_joint_mark_forest_costs_two
#print axioms separate_zero_penalties_do_not_compose
end PureBridgeMarks
