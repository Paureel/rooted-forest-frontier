import ProducerCostAssembly
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer
example : (rawProducer (.leaf [false]) [] [] [] []).work=0 := by decide +kernel
