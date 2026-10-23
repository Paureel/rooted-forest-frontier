import AuditSupport
namespace ToyPrivateAxiom
structure Packet where
  value : Nat
private axiom hidden : Nat
private def hiddenUse : Nat := hidden
theorem harmless : True := True.intro
end ToyPrivateAxiom

audit_local "ToyPrivateAxiom"
