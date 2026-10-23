import SelectedHigh
namespace Universal233.BothBad
open RMAF CoreProgram SourceCoverage PairAssembly BinaryCheap

def outputs (S : Tree) (A B D : List Nat) (q : Nat) : List Output :=
  sideOutputs S B A D q ++ sideOutputs S A B D q

def contained (K A : List Nat) : Bool := K.all (A.contains ·)

def separated (F : List (List Nat)) (A D : List Nat) : Bool :=
  (F.filter (contained · A)).all (fun K =>
    K.all (D.contains ·) || K.all (fun x => !(D.contains x)))

def refinesCheck (F Q : List (List Nat)) : Bool :=
  F.all (fun K => Q.any (fun U => K.all (U.contains ·)))
end Universal233.BothBad
