namespace AuditPlant
axiom hiddenBad : False
private theorem privateLeak : False := hiddenBad
theorem leak : False := privateLeak
#print axioms leak
end AuditPlant
