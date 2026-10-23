import GeometryPositive
open TripleDP TripleDP.GeometryRoute
-- Deliberately false. Compilation must fail specifically at this proposition.
example : jointSupport asymmetricLeft singletonRoot [false,true] := by dsimp [jointSupport, singletonRoot, asymmetricLeft] <;> decide
