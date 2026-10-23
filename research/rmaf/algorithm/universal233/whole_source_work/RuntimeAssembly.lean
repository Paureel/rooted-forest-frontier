import GeometryWork
import OwnershipWork

namespace Universal233.WholeSourceWork
open RMAF VertexGeometry CoreProgram CoreWork WholeSourceMass SourceCoverage

/-- Ordinary q is passed unchanged to every whole-source call. -/
def cliqueConstruction (S T : Tree) (A B C : List Nat) (v : RMAF.Vertex) (q : Nat) : Nat :=
  (meterCliqueSelection T A B C).work+(meterClique S T A B v q).work+4

def chainConstruction (S T : Tree) (A B : List Nat) (v w : RMAF.Vertex) (q : Nat) : Nat :=
  (meterJointColors B T v w).work+(meterChain S T A B v w q).work+4

def diagonalConstruction (S T : Tree) (A B : List Nat) (v w : RMAF.Vertex) (q : Nat) : Nat :=
  (meterJointColors B T v w).work+(meterDiagonal S T A B v w q).work+4

theorem cliqueConstruction_bound (S T A B C v q) :
    cliqueConstruction S T A B C v q ≤ selectionCap T A B C+
      wholeBound S T A B (cliqueColors v).1 q+
      wholeBound S T A B (cliqueColors v).2.1 q+
      wholeBound S T A B (cliqueColors v).2.2 q+3*recordBound S q+8 := by
  have h := meterClique_bound S T A B v q
  have hs := meterCliqueSelection_bound T A B C
  unfold cliqueConstruction
  omega

theorem chainConstruction_bound (S T A B v w q) :
    chainConstruction S T A B v w q ≤ jointGateCap B T v w+
      wholeBound S T A B (chainColors v w).1 q+
      wholeBound S T A B (chainColors v w).2.1 q+
      wholeBound S T A B (chainColors v w).2.2.1 q+
      wholeBound S T A B (chainColors v w).2.2.2 q+6*recordBound S q+10 := by
  have h := meterChain_bound S T A B v w q
  have hs := meterJointColors_bound B T v w
  unfold chainConstruction
  omega

theorem diagonalConstruction_bound (S T A B v w q) :
    diagonalConstruction S T A B v w q ≤ jointGateCap B T v w+
      wholeBound S T A B (chainColors v w).2.1 q+
      wholeBound S T A B (chainColors v w).2.2.1 q+recordBound S q+6 := by
  have h := meterDiagonal_bound S T A B v w q
  have hs := meterJointColors_bound B T v w
  unfold diagonalConstruction
  omega

/-- Exact strict margin of the three COMPLETE displayed macro expressions,
including the two endpoint branches. This is conditional arithmetic, not a
claim that all actual rooted-MAF rules/pair selectors satisfy that recurrence. -/
def runtimeBase : Rat := mkRat 233 100
def cliqueFactor : Rat := 2/runtimeBase+3*runtimeBase^(-4 : Int)
def chainFactor : Rat := 2/runtimeBase+4*runtimeBase^(-4 : Int)
def diagonalFactor : Rat := 2/runtimeBase+runtimeBase^(-3 : Int)+runtimeBase^(-4 : Int)

theorem strict_macro_margins :
    2 < runtimeBase ∧ runtimeBase < mkRat 23391 10000 ∧
      cliqueFactor < 1 ∧ chainFactor < 1 ∧ diagonalFactor < 1 := by
  change 2 < mkRat 233 100 ∧ mkRat 233 100 < mkRat 23391 10000 ∧
    2/mkRat 233 100+3*((mkRat 233 100)^(4 : Nat))⁻¹ < 1 ∧
    2/mkRat 233 100+4*((mkRat 233 100)^(4 : Nat))⁻¹ < 1 ∧
    2/mkRat 233 100+((mkRat 233 100)^(3 : Nat))⁻¹+
      ((mkRat 233 100)^(4 : Nat))⁻¹ < 1
  simp only [Rat.div_def,Rat.inv_def]
  decide +kernel

/-- The strict margin pays an additive normalized construction overhead.
For b≥2, 2^q/b^q≤1; instantiate overhead by its polynomial coefficient.
This algebra lemma makes no assumption about the unproved full algorithm. -/
theorem additive_margin (beta overhead K R : Rat)
    (hmargin : overhead ≤ (1-beta)*K) (hrec : R ≤ beta*K+overhead) : R ≤ K := by
  have he : beta*K+(1-beta)*K = K := by
    grind
  have hsum := qadd_le_add (show beta*K ≤ beta*K from Rat.le_refl) hmargin
  rw [he] at hsum
  exact Rat.le_trans hrec hsum

end Universal233.WholeSourceWork
