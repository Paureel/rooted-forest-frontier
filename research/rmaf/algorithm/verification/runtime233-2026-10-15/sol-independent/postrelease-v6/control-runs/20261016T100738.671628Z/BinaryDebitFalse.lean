import BinaryCallerPayload
open GenericForest.BinaryProvider GenericForest.BinaryCaller
private def z : GenericForest.BinaryProvider.Tree := .leaf []
example : setupCallsWork (some z) [z] [] [[[]],[[]]]=(checkerCapacity (some z) [z] [] [[]]).work := by decide +kernel
