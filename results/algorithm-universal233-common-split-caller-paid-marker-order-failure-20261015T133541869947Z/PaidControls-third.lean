import PaidDefs
import CallerControls
namespace OrdinaryCommonSplit.Caller.PaidControls
open RMAF OrdinaryCommonSplit.Controls
def d : Setup where
  T:=T
  S:=S
  tx:=tX
  sx:=sX
  ty:=tY
  sy:=sY
  mxT:=markedXT
  mxS:=markedXS
  myT:=markedYT
  myS:=markedYS
  X:=X
  Y:=Y
  x:=0
  y:=3
  rho:=6
  gamma:=7
  nt:=by decide
  ns:=by decide
  hpT:=by decide
  hpS:=by decide
  edgeT:=⟨[false],tX,by decide,by decide,Or.inr (by decide)⟩
  edgeS:=⟨[false],sX,by decide,by decide,Or.inr (by decide)⟩
  htx:=by decide
  hsx:=by decide
  hty:=by decide
  hsy:=by decide
  hMXT:=by decide
  hMXS:=by decide
  hMYT:=by decide
  hMYS:=by decide
  hx:=by decide
  hy:=by decide
  frT:=by decide
  frS:=by decide
  fgT:=by decide
  fgS:=by decide
def FX : Forest := [[0,1],[2]]
def FY : Forest := [[3,4],[5]]
def cb (t _s : Tree) (q : Nat) : Option Forest :=
  if q=0 then none else if t=tX then some FX else some Controls.FM
theorem actual_jobs : (paidJobs d 0)=[] ∧ (paidJobs d 2).map Job.budget=[1,1] := by decide
theorem paid_success : replyCost (runPaid d 2 FY Controls.FN cb)=some 2 := by decide
theorem pruned_and_rejected : runPaid d 0 FY Controls.FN cb=none ∧
    runPaid d 1 FY Controls.FN cb=none := by decide
theorem list_reconstruction : replyCost (reconstruct d FX FY Controls.FM Controls.FN)=some 2 := by decide
end OrdinaryCommonSplit.Caller.PaidControls
