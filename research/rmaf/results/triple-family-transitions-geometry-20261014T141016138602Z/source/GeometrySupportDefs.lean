import FamilyAssembly

/-! Independent address-decomposition route. This definition contains no
finite-index operations. Root is always present; a nonempty address selects
exactly its corresponding child predicate. -/
namespace TripleDP.GeometryRoute
open TripleDP TripleDP.CostRoute

def jointSupport (left right : Address → Prop) : Address → Prop
  | [] => True
  | false :: a => left a
  | true :: a => right a

end TripleDP.GeometryRoute
