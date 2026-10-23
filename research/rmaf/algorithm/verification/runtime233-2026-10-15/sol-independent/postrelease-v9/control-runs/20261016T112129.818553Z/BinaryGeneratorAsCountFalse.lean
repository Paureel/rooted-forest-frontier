import ProducerCostAssembly
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer
example : (Generator.generateBits (.leaf [false]) (Generator.colorBits (.leaf [false]) []) []).work=1 := by decide +kernel
