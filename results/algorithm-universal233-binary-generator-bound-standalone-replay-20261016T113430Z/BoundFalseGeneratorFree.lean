import GeneratorBoundControls
open GenericForest.BinaryProducer GenericForest.BinaryProducer.BoundControls GenericForest.BinaryProducer.CostControls GenericForest.BinaryProvider GenericForest.ScalarBits
example : (Generator.generateBits crossed parity []).work=0 := by have h:=actual_prefix_truth.1;omega
