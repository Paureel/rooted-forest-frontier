import BothPrecontrols
open RMAF Universal233.BothBad Universal233.BothBad.Precontrols
example : agreement T S crossBoth=true := by decide
example : separated crossA A D=true := by decide
example : separated crossB B D=true := by decide
example : ((outputs S A B D 2).any (fun o => refinesCheck crossA o.partition))=true := by decide
