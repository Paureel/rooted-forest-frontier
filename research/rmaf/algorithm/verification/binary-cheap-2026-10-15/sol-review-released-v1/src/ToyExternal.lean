import OriginAudit
namespace ToyExternal
axiom importedBad : False
end ToyExternal

run_cmd ReleasedAudit.emit ["ToyExternal"]
