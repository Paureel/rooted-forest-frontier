import FreshConsumer
namespace NonauthorFalseTwins
open RMAF Universal233 CoreProgram KeptParent

def clade : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def crossed : Tree := .node (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.leaf 4)
def color : Nat → Nat := keepColor [0,1] [2] (fun _ => 7)
def crossColor : Nat → Nat := keepColor [0,2] [1,3] (fun _ => 0)
def hasA (o : Output) : Bool := o.partition.any (fun b => b.all ([0,2] : List Nat).contains && ([0,2] : List Nat).all b.contains)
def raw := (generate crossed crossColor 3).outputs
theorem clean0 : pairwiseEmbeddings crossed [[0,2],[1,3],[4]] = false := by decide
theorem clean1 : raw.all hasA = false := by decide
theorem clean2 : (generate clade color 1).outputs = [] := by decide
theorem clean3 : color 2 = 22 := by decide
theorem clean4 : raw.length = 2 := by decide
theorem clean5 : (raw ++ raw).length = 4 := by decide
theorem clean6 : restrict [0,1] clade = some (.node (.leaf 0) (.leaf 1)) := by decide
theorem clean7 : partitionCheck (leaves clade) [[0,1,1],[2],[3]] = false := by decide
theorem clean8 : (⟨[[0],[1,2]],[[false]]⟩ : Output) ∉ (generate NonauthorKeptConsumer.localS NonauthorKeptConsumer.localColor 1).outputs := by decide
theorem clean9 : restrictionAgrees NonauthorKeptConsumer.S NonauthorKeptConsumer.T NonauthorKeptConsumer.A = false := by decide
end NonauthorFalseTwins
