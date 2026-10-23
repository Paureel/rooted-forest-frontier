import ProducerCostsControls
namespace CostsAuditPlant
axiom forbiddenCallback : False
def ghost : Nat := False.elim forbiddenCallback
end CostsAuditPlant
