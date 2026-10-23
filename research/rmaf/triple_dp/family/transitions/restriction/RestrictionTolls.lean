import RestrictionFixtures

namespace TripleDP.Transitions.Restriction.Fixtures

theorem close_toll : R1.cost -
    ((restrict R1 H1 false).cost + (restrict R1 H1 true).cost) = 2 := by
  rw [R1_numbers.2.1, R1_numbers.2.2.2.2.1, R1_numbers.2.2.2.2.2.1]

theorem closed_root_child_cost : (restrict R5 H5 false).cost = 0 :=
  R5_numbers.2.2.2.2.1

theorem unused_root_child_cost : (restrict R6 H6 false).cost = 2 :=
  R6_numbers.2.2.2.2.1

theorem merge_parent_count : R4.blockCount = 1 := R4_numbers.1

theorem extend_unused_toll : R7.cost -
    ((restrict R7 H7 false).cost + (restrict R7 H7 true).cost) = 0 := by
  rw [R7_numbers.2.1, R7_numbers.2.2.2.2.1, R7_numbers.2.2.2.2.2.1]

#print axioms close_toll
#print axioms closed_root_child_cost
#print axioms unused_root_child_cost
#print axioms merge_parent_count
#print axioms extend_unused_toll
end TripleDP.Transitions.Restriction.Fixtures
