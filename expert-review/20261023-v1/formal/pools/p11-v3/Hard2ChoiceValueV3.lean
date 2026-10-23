import OrdinaryFrontValueV3

namespace SourceHard2ValuesV3
open RMAF Universal233 SourceForestV3 OrdinaryDispatch.Hard2SourceWork

theorem choose_value (a b : Option F) : (chooseMeter a b).value=BothBad.choose a b := by
  cases a <;> cases b <;> rfl
end SourceHard2ValuesV3
