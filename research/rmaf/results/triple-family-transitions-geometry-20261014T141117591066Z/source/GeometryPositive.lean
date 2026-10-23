import GeometrySupportDefs
namespace TripleDP.GeometryRoute
open TripleDP TripleDP.CostRoute

def singletonRoot (a : Address) : Prop := a = []
def asymmetricLeft (a : Address) : Prop := a = [] ∨ a = [false] ∨ a = [false,true]

example : jointSupport singletonRoot singletonRoot [] := by dsimp [jointSupport, singletonRoot, asymmetricLeft] <;> decide
example : jointSupport singletonRoot singletonRoot [false] := by dsimp [jointSupport, singletonRoot, asymmetricLeft] <;> decide
example : jointSupport singletonRoot singletonRoot [true] := by dsimp [jointSupport, singletonRoot, asymmetricLeft] <;> decide
example : ¬ jointSupport singletonRoot singletonRoot [false,false] := by dsimp [jointSupport, singletonRoot, asymmetricLeft] <;> decide
example : jointSupport asymmetricLeft singletonRoot [false,false,true] := by dsimp [jointSupport, singletonRoot, asymmetricLeft] <;> decide
example : ¬ jointSupport asymmetricLeft singletonRoot [false,true] := by dsimp [jointSupport, singletonRoot, asymmetricLeft] <;> decide
example : ¬ PathConvex gappedRegion := gapped_region_not_pathConvex
end TripleDP.GeometryRoute
