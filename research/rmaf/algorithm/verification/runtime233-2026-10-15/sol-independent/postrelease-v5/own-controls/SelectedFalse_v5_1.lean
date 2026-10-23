import ForestArmBinding
open RMAF Universal233.Rule5SelectedLocalWork
example : ForestArm (.remaining ⟨[],[],0⟩ (.one [])) := by unfold ForestArm; decide +kernel
