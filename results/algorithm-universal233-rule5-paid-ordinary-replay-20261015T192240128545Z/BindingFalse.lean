import PaymentControls
namespace Universal233.Rule5PaidOrdinary.Controls
open RMAF Rule5PaidSelector
-- Wrong refund of a genuine required current-state cut.
example : currentQuery emptyActual (some ft) fss 0=.answered (some fw) := by decide
-- Omitting every affordable request cannot retain this known feasible case.
example : missingRequests.isSome=true := by decide
-- Three and four actual valid original cuts must all be paid.
example : (requestFor eight eight 5 child3).map PaidRequest.residual=some 3 := by decide
example : (requestFor eight eight 5 child4).map PaidRequest.residual=some 3 := by decide
end Universal233.Rule5PaidOrdinary.Controls
