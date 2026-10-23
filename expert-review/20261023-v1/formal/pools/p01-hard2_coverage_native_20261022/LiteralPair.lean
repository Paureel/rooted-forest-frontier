-- Exact computational declaration slices from frozen Dispatcher/PairExecution;
-- explicit namespace transport is audited separately, no author proof imported.
import ActualPairInputs
open RMAF ForestState ForestGroups RestrictionBridge
namespace ContactedGoodPair
abbrev Forest := List (List Nat)
abbrev Ordinary := Tree → Tree → Nat → Option Forest
structure Call where
 target : Option Tree
 sources : List Tree
 budget : Nat
structure Execution where
 answer : Option Forest
 calls : List Call
def accept (T S : Tree) (q : Nat) (F : Forest) : Bool := agreement T S F && decide (F.length-1≤q)
def checked (T S : Tree) (q : Nat) (o : Option Forest) : Option Forest :=
 o.bind (fun F => if accept T S q F then some F else none)
def runPair (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat) : Execution :=
 if 2≤q then
  let ss := OutputState.sourceForest S [A,B,C]
  match AllGoodDP.run (localTarget (some T) (A++B)) (owned ss (A++B)) with
  | none => ⟨none,[]⟩
  | some H =>
   let m := additionalCost (owned ss (A++B)) H
   if m≤q-2 then
    let r := q-2-m
    let target := localTarget (some T) C
    let sources := owned ss C
    ⟨checked T S q ((GenericForest.solve actual target sources r).map (fun K=>H++K)),[⟨target,sources,r⟩]⟩
   else ⟨none,[]⟩
 else ⟨none,[]⟩
end ContactedGoodPair

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
