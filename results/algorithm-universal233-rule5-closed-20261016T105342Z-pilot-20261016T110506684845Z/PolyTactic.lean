import ConcreteFees
import Lean
namespace Universal233.Rule5ClosedSource
open Lean Elab Tactic

/-- Only decompose matching syntactic polynomial operators. In particular,
never ask unification to invent a power/addition around an atomic goal. -/
elab "poly_step" : tactic => do
 let ty←getMainTarget
 let args:=ty.getAppArgs
 if args.size<2 then throwError "expected an inequality"
 let l:=args[args.size-2]!
 let r:=args[args.size-1]!
 let hl:=l.getAppFn.constName?
 let hr:=r.getAppFn.constName?
 if (hl==some ``HAdd.hAdd || hl==some ``Nat.add) && (hr==some ``HAdd.hAdd || hr==some ``Nat.add) then
  evalTactic (←`(tactic|apply Nat.add_le_add))
 else if (hl==some ``HMul.hMul || hl==some ``Nat.mul) && (hr==some ``HMul.hMul || hr==some ``Nat.mul) then
  evalTactic (←`(tactic|apply Nat.mul_le_mul))
 else if (hl==some ``HPow.hPow || hl==some ``Nat.pow) && (hr==some ``HPow.hPow || hr==some ``Nat.pow) then
  evalTactic (←`(tactic|apply Nat.pow_le_pow_left))
 else
  evalTactic (←`(tactic|omega))

macro "poly_mono" : tactic => `(tactic|repeat first
 | assumption
 | exact Nat.le_refl _
 | poly_step)

example (n N : Nat) (h:n≤N) : 7*(2*n+3)^5+n*n≤7*(2*N+3)^5+N*N := by poly_mono
end Universal233.Rule5ClosedSource
