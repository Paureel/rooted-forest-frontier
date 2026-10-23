import FreshConsumer
namespace NonauthorFalseTwins
open RMAF Universal233 CoreProgram KeptParent

def clade : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def crossed : Tree := .node (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.leaf 4)
def color : Nat → Nat := keepColor [0,1] [2] (fun _ => 7)
def crossColor : Nat → Nat := keepColor [0,2] [1,3] (fun _ => 0)
def hasA (o : Output) : Bool := o.partition.any (fun b => b.all ([0,2] : List Nat).contains && ([0,2] : List Nat).all b.contains)
def raw := (generate crossed crossColor 3).outputs
example : raw.all hasA = true := by decide
end NonauthorFalseTwins
