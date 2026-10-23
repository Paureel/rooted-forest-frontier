import OriginAudit
namespace ToyRestriction
structure Restriction where
  value : Nat
end ToyRestriction

run_cmd ReleasedAudit.emit ["ToyRestriction"]
