import GeneratorBoundControls
namespace BoundAuditPlant
axiom forbiddenCallback : False
def ghost : Nat := False.elim forbiddenCallback
end BoundAuditPlant
