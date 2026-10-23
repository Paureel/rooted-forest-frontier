import RuntimeAssembly
open RMAF Universal233.WholeSourceWork

-- Source-operation caps for the review's explicit conservative contracts.
-- These arithmetic facts are not an extracted operational semantics.
def reviewedWholeBound (S T : Tree) (A B : List Nat) (c : Colors) (q : Nat) : Nat :=
  coreBound S q+64*(taggedCap T A B c*(leaves S).length+64)

theorem reviewedWhole_dominates (S T A B c q) :
    wholeBound S T A B c q ≤ reviewedWholeBound S T A B c q := by
  unfold wholeBound reviewedWholeBound
  omega

theorem reviewedOuter (cells joins : Nat) :
    cells+2*joins ≤ 8*cells+16*joins := by omega

def reviewedClique (S T : Tree) (A B : List Nat) (v : RMAF.Vertex) (q : Nat) : Nat :=
  reviewedWholeBound S T A B (cliqueColors v).1 q+
  reviewedWholeBound S T A B (cliqueColors v).2.1 q+
  reviewedWholeBound S T A B (cliqueColors v).2.2 q+24*recordBound S q+32

def reviewedChain (S T : Tree) (A B : List Nat) (v w : RMAF.Vertex) (q : Nat) : Nat :=
  reviewedWholeBound S T A B (chainColors v w).1 q+
  reviewedWholeBound S T A B (chainColors v w).2.1 q+
  reviewedWholeBound S T A B (chainColors v w).2.2.1 q+
  reviewedWholeBound S T A B (chainColors v w).2.2.2 q+48*recordBound S q+48

def reviewedDiagonal (S T : Tree) (A B : List Nat) (v w : RMAF.Vertex) (q : Nat) : Nat :=
  reviewedWholeBound S T A B (chainColors v w).2.1 q+
  reviewedWholeBound S T A B (chainColors v w).2.2.1 q+8*recordBound S q+16

theorem reviewedClique_meter (S T A B v q) :
    (meterClique S T A B v q).work ≤ reviewedClique S T A B v q := by
  have h := meterClique_bound S T A B v q
  have h1 := reviewedWhole_dominates S T A B (cliqueColors v).1 q
  have h2 := reviewedWhole_dominates S T A B (cliqueColors v).2.1 q
  have h3 := reviewedWhole_dominates S T A B (cliqueColors v).2.2 q
  unfold reviewedClique
  omega

theorem reviewedChain_meter (S T A B v w q) :
    (meterChain S T A B v w q).work ≤ reviewedChain S T A B v w q := by
  have h := meterChain_bound S T A B v w q
  have h1 := reviewedWhole_dominates S T A B (chainColors v w).1 q
  have h2 := reviewedWhole_dominates S T A B (chainColors v w).2.1 q
  have h3 := reviewedWhole_dominates S T A B (chainColors v w).2.2.1 q
  have h4 := reviewedWhole_dominates S T A B (chainColors v w).2.2.2 q
  unfold reviewedChain
  omega

theorem reviewedDiagonal_meter (S T A B v w q) :
    (meterDiagonal S T A B v w q).work ≤ reviewedDiagonal S T A B v w q := by
  have h := meterDiagonal_bound S T A B v w q
  have h1 := reviewedWhole_dominates S T A B (chainColors v w).2.1 q
  have h2 := reviewedWhole_dominates S T A B (chainColors v w).2.2.1 q
  unfold reviewedDiagonal
  omega

#print axioms reviewedWhole_dominates
#print axioms reviewedOuter
#print axioms reviewedClique_meter
#print axioms reviewedChain_meter
#print axioms reviewedDiagonal_meter
