import FourProbe
namespace IndependentClassifierScope
open RMAF Universal233.CoreProgram Universal233.RankConsumer
theorem rank_premise_needed :
 optimizedFourOutputs (.leaf 0) (fun _ => 0) 0 = [] ∧
 (generate (.leaf 0) (fun _ => 0) 0).outputs = [⟨[[0]],[]⟩] := by decide
end IndependentClassifierScope
