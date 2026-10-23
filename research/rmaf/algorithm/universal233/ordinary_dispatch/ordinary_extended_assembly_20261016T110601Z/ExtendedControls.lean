import HardPaidSourceBound
namespace OrdinaryDispatch.ExtendedSourceAssembly.Controls
open RMAF Universal233 CoreProgram Hard2Overlap Hard2PaidLocal
open OrdinaryDispatch.Hard2SourceWork GenericForest.FrontierWork

def emptyCuts : CherryBranching.Candidate:=⟨[],0,1,[]⟩
def noAnswer : Ordinary:=fun _ _ _=>none
def unaffordable : Output:=⟨[[0]],[[false]]⟩

theorem mass_literals_at_two :
 caseMass 2 .disjoint=0 ∧ caseMass 2 (.clique [])=3/16 ∧
 caseMass 2 (.four .abc [] [])=1/4 ∧ caseMass 2 (.diagonal .abc [] [])=3/16 ∧
 caseMass 2 (.pair .abc (.vertex []))=3/16 ∧ caseMass 2 (.pair .abc (.edge ([],[])))=1/8 := by decide +kernel

theorem empty_generation_source :
 (actualOutputsMeter (.leaf 0) (.leaf 0) emptyCuts 9 (.clique [])).work=8 ∧
 (hardPaidSource noAnswer (fun _ _ _=>7) (.leaf 0) (.leaf 0) 9 emptyCuts (.clique [])).work=14 ∧
 (hardPaidSource noAnswer (fun _ _ _=>7) (.leaf 0) (.leaf 0) 9 emptyCuts (.clique [])).value.calls=[] := by decide +kernel

theorem duplicate_unaffordable_source :
 (fullOutputsSource noAnswer (fun _ _ _=>7) (.leaf 0) (.leaf 0) 0 [unaffordable]).work=10 ∧
 (fullOutputsSource noAnswer (fun _ _ _=>7) (.leaf 0) (.leaf 0) 0 [unaffordable,unaffordable]).work=18 ∧
 (fullOutputsSource noAnswer (fun _ _ _=>7) (.leaf 0) (.leaf 0) 0 [unaffordable,unaffordable]).value.calls=[] := by decide +kernel
end OrdinaryDispatch.ExtendedSourceAssembly.Controls
