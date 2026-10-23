import Rule4DefsV2
open RMAF Universal233
namespace ContactedForward
/- Eliminate the exact original Choice constructor; no author proof projection applied. -/
theorem choice_priority_own {T S : Tree} (s : Rule4.Choice T S) : Rule4.Priority T S := by
 cases s with
 | mk raw priority admission => exact priority

theorem choice_admission_own {T S : Tree} (s : Rule4.Choice T S) : Rule4.LocalGuard T S s.raw := by
 cases s with
 | mk raw priority admission => exact admission
end ContactedForward

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedForward.choice_priority_own
#print axioms ContactedForward.choice_priority_own
#check @ContactedForward.choice_admission_own
#print axioms ContactedForward.choice_admission_own
