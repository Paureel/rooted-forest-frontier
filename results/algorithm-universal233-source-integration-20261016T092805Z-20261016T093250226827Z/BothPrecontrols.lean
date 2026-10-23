import BothProgram
namespace Universal233.BothBad.Precontrols
open RMAF
def S : Tree := .node (.node (.node (.leaf 1) (.node (.leaf 2)
    (.node (.node (.leaf 4) (.leaf 6)) (.node (.leaf 5) (.leaf 7))))) (.leaf 3)) (.leaf 8)
def T : Tree := .node (.node (.node (.leaf 1) (.node (.leaf 4) (.leaf 5)))
    (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 6) (.leaf 7)))) (.leaf 8)
def A : List Nat := [1,2,3]
def B : List Nat := [4,5,6,7]
def C : List Nat := [8]
def D : List Nat := [1,4,5]
def crossA : List (List Nat) := [[1,2],[3],[4,5],[6],[7],[8]]
def crossB : List (List Nat) := [[1],[2,3],[4,6],[5],[7],[8]]
def crossBoth : List (List Nat) := [[1,2],[3],[4,6],[5],[7],[8]]
theorem control_source : partitionCheck (leaves S) [A,B,C]=true ∧ pairwiseEmbeddings S [A,B,C]=true := by decide
theorem control_Across : agreement T S crossA=true ∧ separated crossA A D=false ∧ separated crossA B D=true := by decide
theorem control_Bcross : agreement T S crossB=true ∧ separated crossB A D=true ∧ separated crossB B D=false := by decide
theorem control_bothcross_invalid : partitionCheck (leaves S) crossBoth=true ∧
    separated crossBoth A D=false ∧ separated crossBoth B D=false ∧ agreement T S crossBoth=false := by decide
theorem control_cover_A : ((outputs S A B D 5).any (fun o => refinesCheck crossA o.partition))=true := by decide
theorem control_cover_B : ((outputs S A B D 5).any (fun o => refinesCheck crossB o.partition))=true := by decide
theorem control_raw_profile : ((PairAssembly.sideOutputs S B A D 5).map (fun o => o.sourceCuts.length))=[3] ∧
    ((PairAssembly.sideOutputs S A B D 5).map (fun o => o.sourceCuts.length))=[4,4] := by decide
theorem control_lowbudget : outputs S A B D 2=[] := by decide
end Universal233.BothBad.Precontrols
