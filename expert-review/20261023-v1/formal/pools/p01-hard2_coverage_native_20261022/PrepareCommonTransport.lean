-- Explicit narrow generic preparation application after the named raw equation check.
-- Both physical equation origins remain separate; no pool/source proof identity.
import ActualPaidPredicateComplete
import FullStateJobs
open RMAF Universal233 Universal233.PaidQueries Universal233.GroupedFullQuery
namespace ContactedHard2Survival
theorem common_prepare_spec (ps : List Problem) (js : List (Job Problem (List (List Nat))))
 (h : prepare ps=some js) : js.map Job.problem=ps ∧ ∀j,j∈js→GroupedFullQuery.Planned j := by
 exact GroupedFullQuery.prepare_spec ps js h
theorem common_prepare_exists (ps : List Problem)
 (hp : ∀p,p∈ps→ForestState.proper p.target p.sources=true) : ∃js,prepare ps=some js := by
 exact GroupedFullQuery.prepare_exists ps hp
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.common_prepare_spec
#print axioms ContactedHard2Survival.common_prepare_spec
#check @ContactedHard2Survival.common_prepare_exists
#print axioms ContactedHard2Survival.common_prepare_exists
