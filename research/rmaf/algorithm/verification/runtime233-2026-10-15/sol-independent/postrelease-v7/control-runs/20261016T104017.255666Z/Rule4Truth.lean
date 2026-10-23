import Rule4BoundInterface
open OrdinaryDispatch.FullSourceWork
example : rule4LocalPolynomial 0 = 300 := by decide +kernel
example : rule4SourcePolynomial 0 0 = 300+48*(2^50*2^8) := by decide +kernel
