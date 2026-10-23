import Rule4SourceControls
namespace OrdinaryDispatch.FullSourceWork.Rule4Controls
example : (leafAddressMeter 9 C).work=8 := by decide +kernel
example : (rule4AnswersSource refusal (fun _ _ _=>0) 0 [B,B]).work=7 := by decide +kernel
example : (rule4PartitionMeter C [[false],[true]]).value=[[0],[1]] := by decide +kernel
end OrdinaryDispatch.FullSourceWork.Rule4Controls
