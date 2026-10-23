import AuditSupport
import ToyExternal
namespace ToyUseExternal
theorem contaminated : False := ToyExternal.importedBad
end ToyUseExternal

audit_local "ToyUseExternal"
