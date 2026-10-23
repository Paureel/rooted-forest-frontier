import Lean

-- Deliberately compilable false plant: strict axiom audit must reject this module.
axiom pair14_planted_false : False
theorem pair14_contaminated_false_control : False := pair14_planted_false

#print axioms pair14_contaminated_false_control
