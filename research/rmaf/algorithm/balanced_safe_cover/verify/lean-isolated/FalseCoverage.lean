import BalancedCounter
set_option maxRecDepth 10000
-- Planted false claim that the balanced cover retains a two-component optimum.
example : (RMAF.best (fun a => (RMAF.blocks a).length)
    (fun a => RMAF.agreement BalancedCounter.source BalancedCounter.target (RMAF.blocks a)
      && BalancedCounter.refinesCover (RMAF.blocks a))
    (RMAF.assignments 4 4)).map (fun a => (RMAF.blocks a).length) = some 2 := by decide
