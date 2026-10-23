import BinaryProducerControls
open GenericForest.BinaryProducer GenericForest.BinaryProducer.Controls GenericForest.BinaryProvider GenericForest.ScalarBits
example : (disjointProducer noOrdinary pair [.leaf a,.leaf b] q8).work=0 := by dsimp only [disjointProducer];split <;> dsimp only [Charged.work] <;> omega
