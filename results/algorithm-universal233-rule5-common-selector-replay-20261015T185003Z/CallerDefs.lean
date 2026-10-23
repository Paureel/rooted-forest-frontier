import GraphControls
namespace OrdinaryCommonSplit.Caller
open RMAF

/-- The literal output list is generated from actual returned forest lists.
Every possible owner pair is checked; failed guesses are paid local work. -/
def mergeCandidates (X Y : List Nat) (x y rho gamma : Nat)
    (FM FN : List (List Nat)) : List (List (List Nat)) :=
  let GM := relabelForest (swap y rho) FM
  let GN := relabelForest (swap x gamma) FN
  GM.flatMap fun H => GN.map fun J =>
    merged (H.filter (X.contains ·)) (J.filter (Y.contains ·)) (GM.erase H) (GN.erase J)

def pickMerge (T S : Tree) (X Y : List Nat) (x y rho gamma : Nat)
    (FM FN : List (List Nat)) : Option (List (List Nat)) :=
  best (fun G => G.length-1) (agreement T S) (mergeCandidates X Y x y rho gamma FM FN)

def replyCost (o : Option (List (List Nat))) : Option Nat := o.map (fun G => G.length-1)
end OrdinaryCommonSplit.Caller
