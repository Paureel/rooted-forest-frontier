import ProducerCostsControls
open GenericForest.BinaryProducer GenericForest.BinaryProducer.CostControls GenericForest.BinaryProvider GenericForest.ScalarBits
example : (overlapProducer crossed [.leaf z,.leaf z,.leaf a]).value.map overlapValue=some ⟨1,0,[false,false]⟩ := by rw [overlap_truth.1];decide
