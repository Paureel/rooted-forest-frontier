import AuditSupport
import ToyExistingCoverage
namespace ToyCoverageRoute
private def hidden : Bool := ToyExistingCoverage.flag
def identity : Bool := !ToyExistingCoverage.flag
theorem harmless : True := True.intro
end ToyCoverageRoute

audit_local "ToyCoverageTampered"
