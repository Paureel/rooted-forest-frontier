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
theorem control_bad : restrictionAgrees s t a = false ∧ restrictionAgrees s t b = false ∧ restrictionAgrees s t c = true := by decide
theorem control_rank : RankDichotomy.inputRank s color = 4 := by decide
theorem control_cheap : (generate s color 3).outputs.map (fun o => o.sourceCuts.length) = [3] := by decide
theorem control_cheap_classes : (generate s color 3).outputs.map (fun o => o.partition) = [[[1,2],[3,4],[5,6,7,8],[9]]] := by decide
theorem control_both_good : restrictionAgrees s t [1,2] = true ∧ restrictionAgrees s t [3,4] = true := by decide
theorem control_target : pairwiseEmbeddings t [[1,2],[3,4],b,c] = true := by decide
theorem control_other_outputs : (generate s otherColor 7).outputs.all (fun o => o.partition.any (fun k => decide (KeptParent.SameMembers k a)) && o.partition.any (fun k => decide (KeptParent.SameMembers k c))) = true := by decide
-- Same sector geometry, but A's three-label yes sector is deliberately bad.
def sBad : Tree := .node (.node (.node (.leaf 1) (.node (.leaf 2) (.leaf 10))) (.node (.leaf 3) (.leaf 4))) (.node (.node (.leaf 5) (.node (.leaf 6) (.node (.leaf 7) (.leaf 8)))) (.leaf 9))
def tBad : Tree := .node (.node (.node (.node (.node (.leaf 1) (.leaf 2)) (.leaf 10)) (.node (.leaf 5) (.leaf 6))) (.node (.node (.leaf 3) (.leaf 4)) (.node (.leaf 7) (.leaf 8)))) (.leaf 9)
def aBad : List Nat := [1,2,10,3,4]
def dBad : List Nat := [1,2,10,5,6]
def colorBad : Nat → Nat := WholeSourceMass.taggedColor b aBad (fun _ => 0) (sideColor dBad) (fun _ => 0)
theorem control_bad_plant_source : partitionCheck (leaves sBad) [aBad,b,c] = true ∧ pairwiseEmbeddings sBad [aBad,b,c] = true := by decide
theorem control_bad_plant_binary : PairGeometry.choose tBad aBad b = some (.edge ([false],[false,false])) := by decide
theorem control_bad_plant_cheap : (generate sBad colorBad 3).outputs.map (fun o => o.sourceCuts.length) = [3] := by decide
theorem control_bad_sector : restrictionAgrees sBad tBad [1,2,10] = false ∧ restrictionAgrees sBad tBad b = false ∧ disjointVertices tBad [1,2,10] b = true := by decide
-- Overlap alone does not confer source validity.
theorem control_overlap_guard : partitionCheck (leaves t) [a,b,c] = true ∧ pairwiseEmbeddings t [a,b,c] = false := by decide
-- Frozen T1 exchange regression is a development contact, not a new proof.
def oldS : Tree := .node (.node (.node (.leaf 1) (.leaf 2)) (.node (.node (.leaf 3) (.leaf 5)) (.node (.leaf 4) (.leaf 6)))) (.leaf 7)
def oldColor (x : Nat) : Nat := if x ∈ [1,2] then 0 else if x ∈ [3,4,5,6] then 3*(if x∈[1,3,4] then 0 else 1)+1 else 2
def oldF : List (List Nat) := [[1],[2],[3,5],[4],[6],[7]]
def refinesBool (F Q : List (List Nat)) : Bool := F.all fun E => Q.any fun U => E.all U.contains
theorem control_no_original_exchange_refinement : ((generate oldS oldColor 6).outputs.any (fun o => refinesBool oldF o.partition)) = false := by decide
private theorem origin_control : (3 : Nat) < 4 := by decide
theorem control_private_origin : (3 : Nat) < 4 := origin_control
end Universal233.BinaryCheap.Controls
