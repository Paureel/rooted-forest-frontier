import OriginAudit
import ToyExternal
namespace ToyUseExternal
theorem contaminated : False := ToyExternal.importedBad
end ToyUseExternal

run_cmd ReleasedAudit.emit ["ToyUseExternal"]
