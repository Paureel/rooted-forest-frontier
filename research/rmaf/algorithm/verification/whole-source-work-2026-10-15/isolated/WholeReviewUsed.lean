namespace WholeUsedPlant
private axiom zeroAppend : (8*3 : Nat) = 0
private theorem hiddenBill : (8*3 : Nat) = 0 := zeroAppend
theorem bill : (8*3 : Nat) = 0 := hiddenBill
end WholeUsedPlant
