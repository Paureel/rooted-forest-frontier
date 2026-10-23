import ActualPaidThreeCases
import ActualHard2
open RMAF VertexGeometry Universal233 Universal233.CherryBranching
open ContactedHard2Parent ContactedHard2Overlap
namespace ContactedHard2Survival

theorem overlap_original (T : Tree) (A B : List Nat) : Hard2Overlap.overlap T A B=overlap T A B := rfl

theorem first_original (ord : Order) (A B C : List Nat) :
 Hard2Overlap.first (originalOrder ord) A B C=first ord A B C := by cases ord <;>rfl

theorem second_original (ord : Order) (A B C : List Nat) :
 Hard2Overlap.second (originalOrder ord) A B C=second ord A B C := by cases ord <;>rfl

theorem third_original (ord : Order) (A B C : List Nat) :
 Hard2Overlap.third (originalOrder ord) A B C=third ord A B C := by cases ord <;>rfl

theorem chain_original (T : Tree) (A B C : List Nat) (ord : Order) (v w : RMAF.Vertex) :
 Hard2Overlap.chain T A B C (originalOrder ord) v w=originalResult (chain T A B C ord v w) := by
 by_cases h : (jointColors (second ord A B C) T v w).length=2
 · simp only [Hard2Overlap.chain,chain,second_original,ite_eq_left h,originalResult]
 · simp only [Hard2Overlap.chain,chain,second_original,ite_eq_right h,originalResult]

theorem isolated_original (T : Tree) (A B C : List Nat) (ord : Order) :
 Hard2Overlap.isolated T A B C (originalOrder ord)=(isolated T A B C ord).map originalResult := by
 simp only [Hard2Overlap.isolated,isolated,first_original,second_original]
 cases h : PairGeometry.choose T (first ord A B C) (second ord A B C) <;>rfl

theorem select_original (T : Tree) (A B C : List Nat) :
 Hard2Overlap.select T A B C=(select T A B C).map originalResult := by
 simp only [Hard2Overlap.select,ContactedHard2Overlap.select,overlap_original]
 cases ab : overlap T A B <;> cases bc : overlap T B C <;> cases ac : overlap T A C
 · rfl
 · exact isolated_original T A B C .acb
 · exact isolated_original T A B C .bca
 · simpa only [Option.map_some,originalOrder] using congrArg some (chain_original T A B C .acb _ _)
 · exact isolated_original T A B C .abc
 · simpa only [Option.map_some,originalOrder] using congrArg some (chain_original T A B C .bac _ _)
 · simpa only [Option.map_some,originalOrder] using congrArg some (chain_original T A B C .abc _ _)
 · cases h : findCommon (minimalVertices A T) (minimalVertices B T) (minimalVertices C T) <;>rfl

theorem actual_runHard2_original (T S : Tree) (c : Candidate) :
 Hard2Overlap.runHard2 T S c=(ContactedActualHard2.runHard2 T S c).map originalResult := by
 unfold Hard2Overlap.runHard2 ContactedActualHard2.runHard2
 cases h : c.originalCuts with
 | nil=>rfl
 | cons p rest=>
  cases rest with
  | nil=>rfl
  | cons r rest=>
   cases rest with
   | nil=>exact select_original T _ _ _
   | cons x xs=>rfl
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.overlap_original
#print axioms ContactedHard2Survival.overlap_original
#check @ContactedHard2Survival.first_original
#print axioms ContactedHard2Survival.first_original
#check @ContactedHard2Survival.second_original
#print axioms ContactedHard2Survival.second_original
#check @ContactedHard2Survival.third_original
#print axioms ContactedHard2Survival.third_original
#check @ContactedHard2Survival.chain_original
#print axioms ContactedHard2Survival.chain_original
#check @ContactedHard2Survival.isolated_original
#print axioms ContactedHard2Survival.isolated_original
#check @ContactedHard2Survival.select_original
#print axioms ContactedHard2Survival.select_original
#check @ContactedHard2Survival.actual_runHard2_original
#print axioms ContactedHard2Survival.actual_runHard2_original
