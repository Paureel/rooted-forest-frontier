/- A compile-success negative: private unused and opaque-hidden custom axioms. -/
namespace PrecontactAxiom
private axiom neverUsed : Nat
private axiom hidden : Nat
opaque opaqueData : Nat := hidden
theorem harmless : 1 = 1 := rfl
end PrecontactAxiom
