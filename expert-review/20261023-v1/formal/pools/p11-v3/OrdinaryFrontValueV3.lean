import Hard2UnitMetadataV3

namespace SourceOrdinaryFrontV3
open RMAF Universal233 OrdinaryDispatch.EarlyLocalWork
open OrdinaryDispatch.FastOrdinary

-- Direct value calculation of the licensed body; no meterFront wrapper theorem.
theorem front_value (q : Nat) (T S : Tree) :
    (meterFront q T S).value=
      (if DepthOne.proper T S then
        match DepthOne.pretest01 T S with
        | .refused=>.stop none
        | .found c=>.stop (if DepthOne.cutCost c≤q then some (DepthOne.forest S c) else none)
        | .rejected=>.selected (early T S)
       else .stop none) := by
  simp only [meterFront,meterOrdinaryProper_value,meterPretest_value,meterForest_value,meterEarly_value]
  cases DepthOne.proper T S <;> cases DepthOne.pretest01 T S <;> rfl
end SourceOrdinaryFrontV3
