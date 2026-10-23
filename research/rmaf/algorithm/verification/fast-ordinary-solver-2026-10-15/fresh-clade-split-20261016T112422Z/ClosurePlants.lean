namespace ClosurePlants
axiom badAx : False
theorem bad : False := badAx
def forbiddenProbe : Nat := 0
def forbiddenRoot : Nat := forbiddenProbe
unsafe def unsafeProbe : Nat := 0
unsafe def unsafeRoot : Nat := unsafeProbe
axiom typeAx : Type
def typeOnly (x : typeAx) : typeAx := x
end ClosurePlants
