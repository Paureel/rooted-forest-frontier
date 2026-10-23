import ColorClasses

/-! One-shot final recovery of original cuts after the minimum labelled
agreement has been selected. This program scans literal blocks, never set
partitions. Scalar colors are original representative labels. -/
namespace Universal233.FinalCutRecovery
open RMAF CoreProgram

def blockColor : List (List Nat) → Nat → Nat
  | [], _ => 0
  | b :: bs, x => if b.contains x then b.headD 0 else blockColor bs x

def inputCheck (S : Tree) (P : List (List Nat)) : Bool :=
  decide (leaves S).Nodup && partitionCheck (leaves S) P && pairwiseEmbeddings S P

def recover (S : Tree) (P : List (List Nat)) : Option Output :=
  if inputCheck S P then (generate S (blockColor P) (P.length - 1)).outputs.head?
  else none

end Universal233.FinalCutRecovery

-- deliberate source corruption
