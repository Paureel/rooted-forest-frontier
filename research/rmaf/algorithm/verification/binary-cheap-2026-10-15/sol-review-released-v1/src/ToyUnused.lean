import OriginAudit
axiom outside_namespace_unused : False
namespace ToyUnused
theorem harmless : True := True.intro
end ToyUnused

run_cmd ReleasedAudit.emit ["ToyUnused"]
