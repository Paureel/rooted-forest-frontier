import GuardedExact
import GuardedControls
namespace OrdinaryCommonSplit.Caller.GuardRefusalControls
open RMAF Universal233 PaidControls

def equalPair : Setup := { d with
  S:=d.T
  sx:=d.tx
  sy:=d.ty
  mxS:=d.mxT
  myS:=d.myT
  ns:=d.nt
  hpS:=d.hpT
  edgeS:=d.edgeT
  hsx:=d.htx
  hsy:=d.hty
  hMXS:=d.hMXT
  hMYS:=d.hMYT
  frS:=d.frT
  fgS:=d.fgT }

theorem zero_outside_refuses : DepthOne.pretest01 equalPair.ty equalPair.sy=.found none ∧
    runGuarded equalPair 2 cb=none ∧ guardedJobs equalPair 2=[] := by decide
theorem refused_state_has_real_solution : agreement equalPair.T equalPair.S [leaves equalPair.T]=true := by decide
end OrdinaryCommonSplit.Caller.GuardRefusalControls
