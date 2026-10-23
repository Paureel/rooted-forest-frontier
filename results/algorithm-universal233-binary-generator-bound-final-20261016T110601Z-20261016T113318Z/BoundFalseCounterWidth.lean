import GeneratorBoundControls
open GenericForest.BinaryProducer GenericForest.BinaryProducer.BoundControls GenericForest.BinaryProducer.CostControls GenericForest.BinaryProvider GenericForest.ScalarBits
example : (Generator.generateBits crossed parity b).value.visited.length=1 := by rw [actual_prefix_truth.2.2];decide
