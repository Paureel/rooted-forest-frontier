/- Author integration: specialize the saved parametric local proof bodies to
   the actual original solver. No recursive IH or guard is discharged here. -/
import NativeControlsFull
import NativeCommon
namespace LocalNative

theorem one_rule : IndependentReconstruction.OneRule :=
 PaidInstances.one_rule OrdinaryDispatch.FastOrdinary.solve

theorem high_rule : IndependentReconstruction.HighRule :=
 ForestContinuation.high_rule OrdinaryDispatch.FastOrdinary.solve

theorem forward_rule4 : IndependentReconstruction.ForwardRule4 :=
 ContactedForwardCallbacks.forward_rule OrdinaryDispatch.FastOrdinary.solve

theorem reverse_rule4 : IndependentReconstruction.ReverseRule4 :=
 AuthoredReverse.reverse_rule OrdinaryDispatch.FastOrdinary.solve

#print one_rule
#print high_rule
#print forward_rule4
#print reverse_rule4
#print axioms one_rule
#print axioms high_rule
#print axioms forward_rule4
#print axioms reverse_rule4
end LocalNative
