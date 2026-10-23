import GoodPair
import FourProbe
import KeptConsumers
import Witness01
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
namespace Universal233.BinaryCheap.Controls
open RMAF CoreProgram SourceCoverage VertexGeometry BinaryExchange PairAssembly
-- Planted by construction, before universal proof; no census.
def a : List Nat := [1,2,3,4]
def b : List Nat := [5,6,7,8]
def c : List Nat := [9]
def d : List Nat := [1,2,5,6]
def s : Tree := .node (.node (.leaf 1) (.node (.leaf 2) (.node (.leaf 3) (.leaf 4)))) (.node (.node (.leaf 5) (.node (.leaf 6) (.node (.leaf 7) (.leaf 8)))) (.leaf 9))
def t : Tree := .node (.node (.node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 5) (.leaf 6))) (.node (.node (.leaf 3) (.leaf 4)) (.node (.leaf 7) (.leaf 8)))) (.leaf 9)
def color : Nat → Nat := WholeSourceMass.taggedColor b a (fun _ => 0) (sideColor d) (fun _ => 0)
def otherColor : Nat → Nat := WholeSourceMass.taggedColor a b (fun _ => 0) (sideColor d) (fun _ => 0)
theorem control_source : partitionCheck (leaves s) [a,b,c] = true ∧ pairwiseEmbeddings s [a,b,c] = true := by decide
theorem control_binary : PairGeometry.choose t a b = some (.edge ([false],[false,false])) := by decide
#eval (generate s color 3).outputs
end Universal233.BinaryCheap.Controls
