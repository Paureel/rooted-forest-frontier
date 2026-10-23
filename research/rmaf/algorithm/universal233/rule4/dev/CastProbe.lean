import Costs
#check Int.natCast_ofNat
#check Int.natCast_ofNat
#check Int.ofNat_eq_coe
example (c : Rat) : c ^ (-((2:Nat):Int)) = c ^ (-2:Int) := by rfl
