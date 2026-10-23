import HardPaidSourceBound
namespace OrdinaryDispatch.Hard2SourceWork.RemainingControls
open RMAF Universal233 WholeSourceWork CoreWork CoreProgram
open GenericForest.FrontierWork

def one : Tree:=.leaf 7
def dup : Tree:=.node (.leaf 7) (.leaf 7)
def color (fee : Nat) : Nat→Charged Nat:=fun _=>⟨0,fee⟩
def uncut : Output:=⟨[[7]],[]⟩

theorem singleton_output_literal :
 (generatedOutputsMeter one (color 0) 999).value=[uncut] ∧
 0<(generatedOutputsMeter one (color 0) 999).work := by cbv

theorem original_color_fee_paid :
 (generatedOutputsMeter one (color 7) 0).value=(generatedOutputsMeter one (color 0) 0).value ∧
 (generatedOutputsMeter one (color 7) 0).work=(generatedOutputsMeter one (color 0) 0).work+7 := by cbv

theorem duplicate_original_refused :
 (generatedOutputsMeter dup (color 0) 100).value=[] ∧
 0<(generatedOutputsMeter dup (color 0) 100).work := by cbv

theorem clique_keeps_all_three :
 (kindOutputsMeter (.clique []) one one [7] [] 0).value=[uncut,uncut,uncut] ∧
 0<(kindOutputsMeter (.clique []) one one [7] [] 0).work := by cbv

theorem four_chain_keeps_all_four :
 (kindOutputsMeter (.four [] [false]) one one [7] [] 0).value=[uncut,uncut,uncut,uncut] := by cbv

theorem append_copies_left_occurrences :
 (appendOutputsMeter ⟨[uncut,uncut],10⟩ ⟨[uncut],20⟩).value=[uncut,uncut,uncut] ∧
 (appendOutputsMeter ⟨[uncut,uncut],10⟩ ⟨[uncut],20⟩).work=38 := by cbv

theorem disjoint_output_generation_refused :
 (caseOutputsMeter one one [7] [] [] 5 .disjoint).value=[] ∧
 (caseOutputsMeter one one [7] [] [] 5 .disjoint).work=2 := by cbv

theorem unaffordable_output_traversed :
 (fullOutputsSource (fun _ _ _=>none) (fun _ _ _=>0) one one 0 [⟨[[7]],[[false]]⟩]).value.calls=[] ∧
 0<(fullOutputsSource (fun _ _ _=>none) (fun _ _ _=>0) one one 0 [⟨[[7]],[[false]]⟩]).work := by cbv
end OrdinaryDispatch.Hard2SourceWork.RemainingControls
