import ProducerCostAssembly
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer Universal233.WholeSourceWork
private def t : Tree := .leaf [false]
private def o : Output := ⟨[],[[false]]⟩
private def failed (_ : Option Tree) (_ : List Tree) (_ : Bits) : Charged (Option Forest) := ⟨none,7⟩
example : (rawProducer t [] [] [] []).work=5 := by decide +kernel
example : (rawProducer t [] [] [] []).value.length=0 := by decide +kernel
example : (branchesProducer t [] ⟨[],[true],[]⟩ []).work=25 := by decide +kernel
example : (indexedOutputs [] [o,o]).work=9 := by decide +kernel
example : rawCallbackWork failed none [] [true] [([],o),([],o)]=14 := by decide +kernel
example : rawCallbackWork failed none [] [] [([],o),([],o)]=0 := by decide +kernel
example : runCallbackWork (fun (_ : Unit) _=>⟨none,9⟩) [] ([.hard (),.hard ()]:List (Job Unit Unit))=9 := by decide +kernel
example : runCallbackWork (fun (_ : Unit) _=>⟨some ([],()),9⟩) [] ([.hard (),.hard ()]:List (Job Unit Unit))=18 := by decide +kernel
example : (Generator.fuelBits [true] [(),(),()]).value.length=1 := by decide +kernel
example : (Generator.generateBits t (Generator.colorBits t []) [true,true,true]).value.outputs.length=1 := by decide +kernel
