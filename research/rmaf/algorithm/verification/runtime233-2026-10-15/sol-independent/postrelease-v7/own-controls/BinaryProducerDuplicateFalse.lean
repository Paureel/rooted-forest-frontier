import BinaryProducerRaw
open GenericForest.BinaryProducer GenericForest.ScalarBits BinaryProvider
example : ((runBits (fun (_ : Nat) _=>⟨some ([true],5),7⟩) [true] [.hard 1,.hard 1]).value.calls).length = 1 := by decide +kernel
