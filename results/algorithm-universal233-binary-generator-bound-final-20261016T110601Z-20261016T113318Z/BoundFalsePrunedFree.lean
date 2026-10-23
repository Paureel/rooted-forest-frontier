import GeneratorBoundControls
open GenericForest.BinaryProducer GenericForest.BinaryProducer.BoundControls GenericForest.BinaryProducer.CostControls GenericForest.BinaryProvider GenericForest.ScalarBits
example : (Generator.generateBits crossed parity []).value.pruned.length=0 := by rw [actual_prefix_truth.2.1];decide
