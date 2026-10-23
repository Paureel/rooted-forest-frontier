# Timing receipt

The first graph control pilot (13 controls, before the common-cherry control was added) took 0.000879209 seconds inside the process. The final graph run has two traces with four and five states and no search; a linear tenfold allowance projects less than 0.02 seconds, excluding launcher startup. Progress units are verified states in the retained replay JSON. No census or long search is launched.

Credit.lean was used as the isolated Lean pilot. The exact elapsed wall time is retained in `../results/thesis-complexity-review-credit-lean.log`; the remaining Trace.lean file is a fixed finite kernel-evaluation job, monitored with a 10-second initial tool yield. A 60-second overrun would trigger inspection, not an unmeasured overnight run. No theorem status is inferred from elapsed time or exit status.
