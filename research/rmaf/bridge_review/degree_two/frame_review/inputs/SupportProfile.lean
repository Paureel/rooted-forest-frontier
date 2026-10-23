import SupportAlgebra
namespace RestrictionRoute
open RMAF

@[simp] theorem disjoint_nil_left (s : List Vertex) : disjointVertices [] s = true := by simp [disjointVertices]
@[simp] theorem disjoint_nil_right (s : List Vertex) : disjointVertices s [] = true := by simp [disjointVertices]

theorem disjointVertices_comm (a b : List Vertex) : disjointVertices a b = disjointVertices b a := by
  apply Bool.eq_iff_iff.mpr
  simpa only [← apart_iff_disjointVertices] using apart_symm a b

theorem disjoint_shell (r s : Bool) (a b c d : List Vertex) :
    disjointVertices (shell r a b) (shell s c d) =
      (!(r && s) && disjointVertices a c && disjointVertices b d) := by
  apply Bool.eq_iff_iff.mpr
  simp only [← apart_iff_disjointVertices, apart_shell, Bool.and_eq_true]
  cases r <;> cases s <;> simp

theorem minimal_nil_of_span_nil (A : List Nat) (t : Tree)
    (h : rootedSpan A t = []) : minimalVertices A t = [] := by
  induction t with
  | leaf x => simpa only [rootedSpan, minimalVertices] using h
  | node l r hl hr =>
      have he : (rootedSpan A l).isEmpty = true ∧ (rootedSpan A r).isEmpty = true := by
        simp only [rootedSpan] at h
        split at h
        · simpa only [Bool.and_eq_true] using ‹((rootedSpan A l).isEmpty && (rootedSpan A r).isEmpty) = true›
        · contradiction
      have hrl : rootedSpan A r = [] := List.isEmpty_iff.mp he.2
      simp [minimalVertices, he.1, hr hrl, prependSide]

theorem rootedSpan_node_shell (A : List Nat) (l r : Tree) :
    rootedSpan A (.node l r) =
      shell (!((rootedSpan A l).isEmpty && (rootedSpan A r).isEmpty))
        (rootedSpan A l) (rootedSpan A r) := by
  cases hl : (rootedSpan A l).isEmpty <;> cases hr : (rootedSpan A r).isEmpty <;>
    simp_all [rootedSpan, shell, List.isEmpty_iff, prependSide]

theorem minimalVertices_node_shell (A : List Nat) (l r : Tree) :
    minimalVertices A (.node l r) =
      if (rootedSpan A l).isEmpty then shell false [] (minimalVertices A r)
      else if (rootedSpan A r).isEmpty then shell false (minimalVertices A l) []
      else shell true (rootedSpan A l) (rootedSpan A r) := by
  simp only [minimalVertices]
  split <;> simp_all [shell, prependSide]

structure PairProfile where
  emptyA : Bool
  emptyC : Bool
  rootMin : Bool
  minRoot : Bool
  minMin : Bool
  deriving DecidableEq, Repr

def supportProfile (A C : List Nat) (t : Tree) : PairProfile :=
  ⟨(rootedSpan A t).isEmpty, (rootedSpan C t).isEmpty,
    disjointVertices (rootedSpan A t) (minimalVertices C t),
    disjointVertices (rootedSpan C t) (minimalVertices A t),
    disjointVertices (minimalVertices A t) (minimalVertices C t)⟩

def emptyProfile : PairProfile := ⟨true,true,true,true,true⟩

def joinProfile (p q : PairProfile) : PairProfile :=
  let aBoth := !p.emptyA && !q.emptyA
  let cBoth := !p.emptyC && !q.emptyC
  ⟨p.emptyA && q.emptyA, p.emptyC && q.emptyC,
    if cBoth then p.emptyA && q.emptyA else p.rootMin && q.rootMin,
    if aBoth then p.emptyC && q.emptyC else p.minRoot && q.minRoot,
    if aBoth then (if cBoth then false else p.rootMin && q.rootMin)
    else if cBoth then p.minRoot && q.minRoot else p.minMin && q.minMin⟩

theorem joinProfile_comm (p q : PairProfile) : joinProfile p q = joinProfile q p := by
  simp only [joinProfile, Bool.and_comm]

theorem joinProfile_empty (p : PairProfile) : joinProfile emptyProfile p = p := by
  cases p
  simp [joinProfile, emptyProfile]

theorem supportProfile_empty (A C : List Nat) (t : Tree)
    (ha : rootedSpan A t = []) (hc : rootedSpan C t = []) :
    supportProfile A C t = emptyProfile := by
  simp [supportProfile, emptyProfile, ha, hc, minimal_nil_of_span_nil A t ha,
    minimal_nil_of_span_nil C t hc]

theorem supportProfile_node (A C : List Nat) (l r : Tree) :
    supportProfile A C (.node l r) = joinProfile (supportProfile A C l) (supportProfile A C r) := by
  have eaL : (rootedSpan A l).isEmpty = true → rootedSpan A l = [] := List.isEmpty_iff.mp
  have eaR : (rootedSpan A r).isEmpty = true → rootedSpan A r = [] := List.isEmpty_iff.mp
  have ecL : (rootedSpan C l).isEmpty = true → rootedSpan C l = [] := List.isEmpty_iff.mp
  have ecR : (rootedSpan C r).isEmpty = true → rootedSpan C r = [] := List.isEmpty_iff.mp
  have maL := minimal_nil_of_span_nil A l
  have maR := minimal_nil_of_span_nil A r
  have mcL := minimal_nil_of_span_nil C l
  have mcR := minimal_nil_of_span_nil C r
  cases haL : (rootedSpan A l).isEmpty <;> cases haR : (rootedSpan A r).isEmpty <;>
    cases hcL : (rootedSpan C l).isEmpty <;> cases hcR : (rootedSpan C r).isEmpty <;>
    simp_all only [Bool.false_eq_true, false_implies, true_implies]
  all_goals simp_all only [supportProfile, joinProfile, rootedSpan_node_shell,
    minimalVertices_node_shell, Bool.false_eq_true,
    Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and, Bool.and_true,
    Bool.and_false, ite_true, ite_false, disjoint_shell, disjoint_nil_left, disjoint_nil_right,
    List.isEmpty_nil]
  all_goals simp [shell, prependSide, disjointVertices_comm]

end RestrictionRoute
