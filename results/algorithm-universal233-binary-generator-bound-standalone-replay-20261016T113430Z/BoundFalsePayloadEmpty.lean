import GeneratorBoundControls
open GenericForest.BinaryProducer GenericForest.BinaryProducer.BoundControls GenericForest.BinaryProducer.CostControls GenericForest.BinaryProvider GenericForest.ScalarBits
example : ((Generator.generateBits crossed parity b).value.outputs.headD ⟨[],[]⟩).partition.flatten.length=0 := by rw [generated_storage_truth.2.1];decide
