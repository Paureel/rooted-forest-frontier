import ForestCallerSetup
open GenericForest.BinaryProducer GenericForest.BinaryProducer.CostControls GenericForest.BinaryProvider
private def altern : Tree := .node (.node (.leaf z) (.leaf b)) (.node (.leaf a) (.leaf c))
private def crossSources : List Tree := [.node (.leaf z) (.leaf b),.node (.leaf a) (.leaf c)]
private def refusal (_ _ : Tree) (_ : Bits) : Universal233.WholeSourceWork.Charged (Option GenericForest.BinaryProvider.Forest):=⟨none,777⟩
#eval forestOptionValue (forestFromInput refusal (some crossed) [altern] b).value
#eval forestOptionValue (forestFromInput refusal (some crossed) crossSources b).value
#eval (forestFromInput refusal (some crossed) crossSources b).work
#eval GenericForest.BinaryProducer.Generator.receiptCells (GenericForest.BinaryProducer.Generator.generateBits crossed parity b).value
#eval GenericForest.BinaryProducer.Generator.generateRetention crossed parity b
