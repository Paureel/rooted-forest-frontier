import ParentTransport
import YieldTransport
import SecondCut
open SecondExchange

namespace ParentControls

def parent : Nat → Option Nat
  | 0 => none
  | 1 => some 0
  | 2 => some 1
  | 3 => some 2
  | 4 => some 3
  | 5 => some 4
  | 6 => some 4
  | 7 => some 3
  | 8 => some 2
  | 9 => some 1
  | _ => none

def b (e : Nat) : Bool := e == 6 || e == 7

example : secondCut (fun e : Nat => e == 2 || e == 9) 9 2 1 true 1 = true := by decide
example : secondCut (fun e : Nat => e == 2 || e == 9) 9 2 1 false 1 = false := by decide
example : secondCut (fun e : Nat => e == 2) 9 2 1 true 1 = false := by decide

def yieldedParent := splice (splice (cutParent b parent) 4 5) 3 5
example : yieldedParent 9 = some 1 := by decide
example : yieldedParent 2 = some 1 := by decide
example : yieldedParent 1 = some 0 := by decide
example : yieldedParent 5 = some 2 := by decide
example : yieldedParent 3 = none := by decide
example : splice (splice (cutParent b (cutParent (fun e => e == 1) parent)) 4 5) 3 5 1 = none := by decide

theorem residual_cut_control :
    cutParent (fun e => e == 2) yieldedParent =
      splice (splice (cutParent (fun e => b e || e == 2) parent) 4 5) 3 5 := by
  exact two_splices_cut_commute parent b (fun e => e == 2) 4 5 3 5
    (by decide) (by decide) (by decide) (by decide)
end ParentControls

namespace TreeControls
open YieldModel

def atom (id label : Nat) : MarkedTree := .node id (some label) false .empty .empty
def a := atom 5 1
def b₁ := atom 6 2
def b₂ := atom 7 3
def c := atom 8 4
def x := atom 9 5

def outerBase (cutU : Bool) : Context :=
  .left 1 none false (.left 2 none cutU .hole c) x

def lowerBase (cutU : Bool) : Context :=
  .left 1 none false (.left 2 none cutU (.left 3 none false .hole (rootMark true b₂)) c) x

def withRho (rho : Bool) (context : Context) : Context :=
  if rho then .left 0 (some 0) false context .empty else context

def source (rho cutU : Bool) : MarkedTree :=
  plug (withRho rho (lowerBase cutU)) (.node 4 none false a (rootMark true b₁))
def middle (rho cutU : Bool) : MarkedTree :=
  plug (withRho rho (outerBase cutU)) (.node 3 none false a (rootMark true b₂))
def target (rho cutU : Bool) : MarkedTree := plug (withRho rho (outerBase cutU)) a

theorem lower_splice (rho cutU : Bool) : PendantSplice (source rho cutU) (middle rho cutU) b₁ := by
  cases rho <;> exact .right _ 4 a b₁

theorem upper_splice (rho cutU : Bool) : PendantSplice (middle rho cutU) (target rho cutU) b₂ :=
  .right _ 3 a b₂

theorem yielded_forest_control (rho cutU : Bool) :
    total (evaluate (source rho cutU)) =
      add (total (evaluate (target rho cutU))) (add (total (evaluate b₁)) (total (evaluate b₂))) :=
  two_splice_yield (lower_splice rho cutU) (upper_splice rho cutU)

#print axioms yielded_forest_control
#print axioms ParentControls.residual_cut_control
end TreeControls
