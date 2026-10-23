import Rule5CanonicalChildrenV3

namespace SourceGroupedRetainsV3
open RMAF Universal233

-- Exactly the active projection of OutputResult's nested MeterReceipt:
-- retain its tag, Receipt answers/calls/visits, and ordered queries;
-- callerWork and recursiveWork are the two explicitly omitted fields.
def OutputRetains : BothBadGrouped.OutputResult→BothBadGrouped.OutputResult→Prop
  | .unaffordable,.unaffordable=>True
  | .refused,.refused=>True
  | .scheduled a,.scheduled b=>a.value=b.value ∧ a.queries=b.queries
  | _,_=>False

theorem refl (a : BothBadGrouped.OutputResult) : OutputRetains a a := by
  cases a with
  | unaffordable => trivial
  | refused => trivial
  | scheduled r => exact ⟨rfl,rfl⟩
end SourceGroupedRetainsV3
