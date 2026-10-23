import GuardedDefs
import OutsideControls
namespace OrdinaryCommonSplit.Caller.GuardedControls
open PaidControls
theorem actual_answer : (runGuarded d 2 cb).map replyCost=some (some 2) := by decide
theorem qzero_is_negative_not_refusal : runGuarded d 0 cb=some none := by decide
theorem actual_guarded_jobs : (guardedJobs d 2).map Job.budget=[1,1] ∧ guardedJobs d 0=[] := by decide
end OrdinaryCommonSplit.Caller.GuardedControls
