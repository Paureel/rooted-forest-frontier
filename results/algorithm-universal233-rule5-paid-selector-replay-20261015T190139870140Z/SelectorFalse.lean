import SelectorControls
namespace Universal233.Rule5PaidSelector.Controls
open RMAF Rule5Local Rule5Local.Pre Rule5FinalClassification
example : (buildSelected sixT sixS 0 1).isSome=false := by decide
example : (buildForSecond sixT sixS 0 1 d v u).isSome=true := by decide
example : (buildForSecond sixT sixS 0 1 ⟨d.badArc,d.singletonArc,99⟩ u v).isSome=true := by decide
example : (omittedRows.findSome? (buildOne sixT sixS 0 1 d u v)).isSome=true := by decide
end Universal233.Rule5PaidSelector.Controls
