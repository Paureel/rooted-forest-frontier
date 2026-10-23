import PaidControls
import ExtractionRootControls
open RMAF Universal233.Rule5Case322 Universal233.Case322Extraction
open Universal233.Case322PaidGuard Universal233.Case322PaidGuard.Controls
example : (guardedPlan core0).map paid = [2,1,2] := by decide
example : (guardedPlan ii0).map paid = [2,1,2] := by decide
open Universal233.Case322Extraction.Controls
example : currentGuard falseBindingT falseBindingS (bBranch falseBindingS 1 [false,true]) = true := by decide
example : (rawPlan rootT rootS 0 1 2 [false,false] [true] [false,true] [true,false]).all (currentGuard rootT rootS) = true := by decide
