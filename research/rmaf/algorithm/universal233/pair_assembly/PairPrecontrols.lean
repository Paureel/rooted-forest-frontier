import Interface
import CoreProgram
import RationalMass
namespace Universal233.PairAssembly.Controls
open RMAF CoreProgram SourceCoverage

def s : Tree := .node (.node (.node (.leaf 1) (.leaf 2)) (.node (.node (.leaf 3) (.leaf 5)) (.node (.leaf 4) (.leaf 6)))) (.leaf 7)
def t : Tree := .node (.node (.node (.leaf 1) (.node (.leaf 3) (.leaf 4))) (.node (.leaf 2) (.node (.leaf 5) (.leaf 6)))) (.leaf 7)
def a : List Nat := [1,2]
def b : List Nat := [3,4,5,6]
def c : List Nat := [7]
def d : List Nat := [1,3,4]
def color (x : Nat) : Nat :=
  if x ∈ a then 0 else if x ∈ b then 3*(if x∈d then 0 else 1)+1 else 2

def originalF : List (List Nat) := [[1],[2],[3,5],[4],[6],[7]]
def refinesBool (F Q : List (List Nat)) : Bool := F.all fun E => Q.any fun U => E.all U.contains

theorem control_actual_selector : PairGeometry.choose t a b = some (.edge ([false],[false,false])) := by decide
theorem control_actual_exchange : BinaryExchange.exchange a b originalF (.node (.leaf 1) (.node (.leaf 3) (.leaf 4))) =
    [[1,2],[3],[5],[4],[6],[7]] := by decide
theorem control_original_exchange_agreements : agreement s t originalF = true ∧
    agreement s t [[1,2],[3],[5],[4],[6],[7]] = true := by decide
theorem control_actual_generator_costs :
    (generate s color 6).outputs.map (fun o => o.sourceCuts.length) = [4,4] := by decide
theorem control_distinct_colors : (dedupNat ((leaves s).map color)).length = 4 := by decide
theorem control_original_not_coverage_witness :
    ((generate s color 6).outputs.any (fun o => refinesBool originalF o.partition)) = false := by decide
end Universal233.PairAssembly.Controls
