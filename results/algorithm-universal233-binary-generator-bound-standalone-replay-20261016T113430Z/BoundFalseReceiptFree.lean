import GeneratorBoundControls
open GenericForest.BinaryProducer GenericForest.BinaryProducer.BoundControls GenericForest.BinaryProducer.CostControls GenericForest.BinaryProvider GenericForest.ScalarBits
example : Generator.receiptCells (Generator.generateBits crossed parity b).value=0 := by rw [concrete_receipt_truth.1];decide
