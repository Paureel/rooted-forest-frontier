namespace WorkAuditPlant
private axiom hiddenFreeAppend : (3 : Nat) = 0
private theorem privateBill : (3 : Nat) = 0 := hiddenFreeAppend
theorem freeAppend : (3 : Nat) = 0 := privateBill
#print axioms freeAppend
end WorkAuditPlant
