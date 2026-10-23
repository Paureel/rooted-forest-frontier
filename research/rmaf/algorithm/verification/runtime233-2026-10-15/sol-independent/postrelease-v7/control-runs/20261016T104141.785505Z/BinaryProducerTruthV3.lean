import BinaryProducerRaw
open GenericForest.BinaryProducer GenericForest.ScalarBits GenericForest.BinaryProvider
example : decode (allocationBits [false,true,false,true] [true,true] [false,true]).value = 5 := by decide +kernel
example : ((runBits (fun (_ : Nat) _=>⟨(none : Option (Bits×Nat)),7⟩) [true] [.hard 1,.hard 1]).value.calls).length = 1 := by decide +kernel
example : (runBits (fun (_ : Nat) _=>⟨(none : Option (Bits×Nat)),7⟩) [true] [.hard 1,.hard 1]).work = 15 := by decide +kernel
example : decode (runBits (fun (_ : Nat) _=>⟨some ([true],5),7⟩) [true] [.hard 1,.hard 1]).value.visits = 2 := by decide +kernel
example : ((runBits (fun (_ : Nat) _=>⟨some ([true],5),7⟩) [true] [.hard 1,.hard 1]).value.calls).length = 2 := by decide +kernel
example : (sourceForestBits (.leaf [true]) [[],[[true]],[[true]]]).value.length = 2 := by decide +kernel
example : (replaceBits [[]] [false,false] [.leaf [true],.leaf [false,true]]).value = [.leaf [false,true]] := by decide +kernel
example : (rawCandidates (fun _ _ _=>⟨none,0⟩) none [] [] [([],⟨[],[]⟩),([],⟨[],[]⟩)]).value.length = 0 := by decide +kernel
example : (rawCandidates (fun _ _ _=>⟨none,0⟩) none [] [] [([],⟨[],[]⟩),([],⟨[],[]⟩)]).work > (rawCandidates (fun _ _ _=>⟨none,0⟩) none [] [] [([],⟨[],[]⟩)]).work := by decide +kernel
