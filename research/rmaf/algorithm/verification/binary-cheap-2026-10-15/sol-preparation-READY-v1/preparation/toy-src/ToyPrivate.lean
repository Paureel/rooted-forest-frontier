import OriginAudit
namespace ToyPrivate
structure Packet where
  value : Nat
private axiom hidden : Nat
private noncomputable def hiddenUse : Nat := hidden
theorem harmless : True := True.intro
end ToyPrivate

run_cmd ReleasedAudit.emit ["ToyPrivate"]
