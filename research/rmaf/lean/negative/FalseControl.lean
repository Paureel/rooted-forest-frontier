import RMAF

/- Deliberate negative control; this file must fail and is not a library target. -/
example : RMAF.agreement RMAF.Controls.leftTree RMAF.Controls.leftTree
    [[0, 2], [1, 3]] = true := by decide
