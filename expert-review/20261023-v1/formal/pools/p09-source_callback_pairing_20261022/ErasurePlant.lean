import OccurrenceLaws
open RMAF OrdinaryDispatch CallbackPairingAuthor
-- Deliberately false: refused visible value is incorrectly treated as zero child work.
#guard WorkRecursion.forestWork paid (fun _ _ _ => 17) (some t) [s] 2 ==
  WorkRecursion.forestWork paid (fun _ _ _ => 0) (some t) [s] 2
