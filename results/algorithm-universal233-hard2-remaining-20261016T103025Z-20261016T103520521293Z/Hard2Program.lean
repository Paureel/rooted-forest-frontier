import Hard2ConsumersV2
namespace OrdinaryDispatch.Hard2Dispatcher
open RMAF ForestState RestrictionBridge Universal233 Universal233.BothBad
open Universal233.CherryBranching Universal233.Hard2Overlap

def rule5Answer (actual : Ordinary) (T S : Tree) (a b q : Nat) : Option Forest :=
 match Rule5OrdinaryDispatch.dispatch actual T S a b q with
 | .answered answer => answer
 | _ => none

/-- The actual target graph and original good/bad predicates determine the
whole-source paid call. Source parents stay the selected original parents. -/
def paidCase (actual : Ordinary) (T S : Tree) (c : Candidate) (q : Nat) (out : Result) : Execution :=
 match c.originalCuts with
 | [p,r] =>
  let A := PaidAssembly.leftParent S p
  let B := PaidAssembly.rightParent S r
  let C := PaidAssembly.rootParent S p r
  match out with
  | .pair o (.edge edge) =>
   let X := first o A B C
   let Y := second o A B C
   let Z := third o A B C
   if restrictionAgrees S T X && restrictionAgrees S T Y then
    GoodPairDP.runPair actual T S X Y Z q
   else if restrictionAgrees S T X || restrictionAgrees S T Y then
    Hard2PaidLocal.runHardPaid actual T S q c out
   else badPair actual T S X Y Z edge q
  | _ => Hard2PaidLocal.runHardPaid actual T S q c out
 | _ => ⟨none,[]⟩

/-- Actual hard2 dispatcher. The reverse candidate is proof context for the
printed priority/admission theorem; the runtime uses the selected forward c. -/
def run (actual : Ordinary) (T S : Tree) (c _d : Candidate) (q : Nat) : Option Forest :=
 match runHard2 T S c with
 | none => none
 | some .disjoint =>
  let P := pendantPartition S c.a c.b
  if P.all (restrictionAgrees T S) then DisjointParents.direct P q
  else if (P.filter (restrictionAgrees T S)).length=2 then rule5Answer actual T S c.a c.b q
  else DisjointParents.run actual T S c.a c.b q
 | some out => (Hard2Combine.combine actual T S c.a c.b q (paidCase actual T S c q out)).answer
end OrdinaryDispatch.Hard2Dispatcher
