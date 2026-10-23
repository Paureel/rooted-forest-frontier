import OriginAudit
import ToyDepthRestriction
namespace ToyRoute
structure Packet where
  value : Nat
private def hiddenId (r : ToyDepthRestriction.DepthRestriction) : ToyDepthRestriction.DepthRestriction := r
def identity (r : ToyDepthRestriction.DepthRestriction) : ToyDepthRestriction.DepthRestriction := r
def projected (r : ToyDepthRestriction.DepthRestriction) : Nat := r.value + 1
theorem harmless : True := True.intro
end ToyRoute

run_cmd ReleasedAudit.emit ["ToyTampered"]
