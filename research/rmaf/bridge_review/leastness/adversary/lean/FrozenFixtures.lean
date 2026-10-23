import RMAF
namespace LeastnessAdversary
set_option maxRecDepth 10000
theorem FrozenFixtures_0 : RMAF.minimalVertices [1, 3] (.node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 3) (.leaf 4))) = [[], [false], [false, false], [true], [true, false]] := by decide
#print axioms FrozenFixtures_0
theorem FrozenFixtures_1 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 3) (.leaf 4))) = [[false, false]] := by decide
#print axioms FrozenFixtures_1
theorem FrozenFixtures_2 : RMAF.minimalVertices [1, 2] (.node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 3) (.leaf 4))) = [[false], [false, false], [false, true]] := by decide
#print axioms FrozenFixtures_2
theorem FrozenFixtures_3 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 3) (.leaf 4))) = [] := by decide
#print axioms FrozenFixtures_3
theorem FrozenFixtures_4 : RMAF.minimalVertices [9] (.node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 3) (.leaf 4))) = [] := by decide
#print axioms FrozenFixtures_4
theorem FrozenFixtures_5 : RMAF.minimalVertices [1] (.leaf 1) = [[]] := by decide
#print axioms FrozenFixtures_5
theorem FrozenFixtures_6 : RMAF.minimalVertices [] (.leaf 1) = [] := by decide
#print axioms FrozenFixtures_6
theorem FrozenFixtures_7 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 2) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, true]] := by decide
#print axioms FrozenFixtures_7
theorem FrozenFixtures_8 : RMAF.minimalVertices [1, 1, 2, 2] (.node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 3) (.leaf 4))) = [[false], [false, false], [false, true]] := by decide
#print axioms FrozenFixtures_8
theorem FrozenFixtures_9 : RMAF.minimalVertices [1, 2] (.node (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)) (.leaf 4)) = [[false, false], [false, false, false], [false, false, true]] := by decide
#print axioms FrozenFixtures_9
end LeastnessAdversary
