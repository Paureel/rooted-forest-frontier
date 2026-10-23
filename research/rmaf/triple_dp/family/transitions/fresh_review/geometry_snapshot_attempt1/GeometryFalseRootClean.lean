import GeometryPositive
open TripleDP TripleDP.GeometryRoute
-- Deliberately false. Compilation must fail specifically at this proposition.
example : jointSupport singletonRoot singletonRoot [] := by dsimp [jointSupport, singletonRoot, asymmetricLeft] <;> decide
