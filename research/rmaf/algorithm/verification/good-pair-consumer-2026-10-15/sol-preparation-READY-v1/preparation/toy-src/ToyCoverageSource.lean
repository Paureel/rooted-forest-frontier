import AuditSupport
import ToyCoverage
namespace ToyCoverageRoute
private def hidden : Bool := ToyCoverage.flag
def identity : Bool := ToyCoverage.flag
theorem harmless : True := True.intro
end ToyCoverageRoute

audit_local "ToyCoverageSource"
