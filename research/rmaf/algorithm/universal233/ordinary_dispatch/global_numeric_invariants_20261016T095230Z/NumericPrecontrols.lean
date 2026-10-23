import OrdinaryStepBounds
import FreshEnvelope
namespace OrdinaryDispatch.GlobalNumeric
example : 8-3=5 := by decide
example : 2<8 := by decide
example (q r n m : Nat) (hq : r≤q) (hn : m≤n) (strict : r=q→m<n) : r+m<q+n := by omega
example : ¬(0+20≤(0+1 : Nat)) := by decide
end OrdinaryDispatch.GlobalNumeric
