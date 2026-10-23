import Std
namespace ReviewRepair
theorem sufficient_local_repair (x ia ib ic : Int)
    (ha : ia ≤ 4*x-2) (hb : ib ≤ 2*x-3) (hc : ic ≤ 2*x-1) :
    1+ia+ib+ic ≤ 8*x-5 := by omega
theorem parent_room (x : Int) : 8*x-5 ≤ 8*x-2 := by omega
#print axioms sufficient_local_repair
#print axioms parent_room
end ReviewRepair
