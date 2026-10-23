import Rule4Solve
import Lean
open RMAF Lean Universal233.Rule4
def crossT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def crossS : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
def crossQ : List (List Nat) := [[0,2],[1,3]]
def singles : List (List Nat) := [[0],[1],[2],[3]]
def ss := OutputState.sourceForest crossS crossQ
def main : IO Unit := do
  IO.println <| (Json.mkObj [
    ("target_Q_embeddings",toJson (pairwiseEmbeddings crossT crossQ)),
    ("source_Q_embeddings",toJson (pairwiseEmbeddings crossS crossQ)),
    ("proper",toJson (ForestState.proper (some crossT) ss)),
    ("state_agrees",toJson (ForestState.agrees (some crossT) ss singles)),
    ("missing_source_agrees",toJson (ForestState.agrees (some crossT) (ss.dropLast) singles)),
    ("absent_raw_guard",toJson (decide (LocalGuard crossT crossS ⟨99,1,2,[false,true],[true,true]⟩))),
    ("root_cut_partition",toJson (partitionCheck (leaves crossS) (literalPartition crossS [[]]))),
    ("root_cut_filtered_state_proper",toJson (ForestState.proper (some crossT) (OutputState.sourceForest crossS (literalPartition crossS [[]])))),
    ("duplicate_cut_partition",toJson (partitionCheck (leaves crossS) (literalPartition crossS [[false,true],[false,true]]))),
    ("absent_cut_partition",toJson (partitionCheck (leaves crossS) (literalPartition crossS [[true,true,true,true]]))),
    ("comparable_cut_partition",toJson (partitionCheck (leaves crossS) (literalPartition crossS [[true],[true,true]])))
  ]).compress
