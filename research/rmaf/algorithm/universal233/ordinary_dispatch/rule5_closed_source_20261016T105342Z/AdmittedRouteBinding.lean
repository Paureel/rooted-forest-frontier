import ActualCaller
namespace Universal233.Rule5ClosedSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5ExecutionSource
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion OrdinaryDispatch.FastOrdinary OrdinaryDispatch.Hard2SourceWork
open WholeSourceWork CoreWork GenericForest.CheckCorrespondence GenericForest.FrontierWork
open Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5Local Rule5SelectedLocalWork
open ClassifierCheckFee PaidLiteralDecisionWork CherryBranching Hard2Overlap

/-- The actual graph/front guard supplies both literals consumed by the
existing admission theorem. No user-supplied Rule5 admission is assumed. -/
theorem admitted_route_facts (T S : Tree) (c : Candidate) (q : Nat)
 (route:(hard2FrontMeter T S c q).value=.admittedRule5) :
 runHard2 T S c=some .disjoint ∧ ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2 := by
 cases hg:runHard2 T S c with
 | none=>simp [hard2FrontMeter,hg] at route
 | some out=>cases out with
  | disjoint=>
   simp only [hard2FrontMeter,runHard2Meter_value,hg,partition_value,meterAll_value,meterRestrictionAgrees_value,meterFilter_value] at route
   split at route
   · contradiction
   · split at route
     · exact ⟨rfl,by assumption⟩
     · contradiction
  | clique v=>simp [hard2FrontMeter,hg] at route
  | four o v w=>simp [hard2FrontMeter,hg] at route
  | diagonal o v w=>simp [hard2FrontMeter,hg] at route
  | pair o choice=>simp [hard2FrontMeter,hg] at route

theorem actual_admitted_route {T S : Tree} {c d : Candidate} (q : Nat)
 (hp:DepthOne.proper T S=true)
 (forward:CherryBranching.select T S=some (.hard2,c))
 (reverse:CherryBranching.select S T=some (.hard2,d))
 (noT:Rule4.select T S=none) (noS:Rule4.select S T=none)
 (route:(hard2FrontMeter T S c q).value=.admittedRule5) :
 admitted T S c.a c.b=true := by
 have f:=admitted_route_facts T S c q route
 exact (actual_disjoint_admission_iff hp forward reverse noT noS f.1).2 f.2

def admittedRouteSource (W : OrdinaryWork) (T S : Tree) (c : Candidate) (q : Nat) :=actualRule5Source W T S c.a c.b q

theorem admitted_route_value (W : OrdinaryWork) (T S : Tree) (c : Candidate) (q : Nat) :
 (admittedRouteSource W T S c q).value=executeHard2Route (actualCallback q) T S c q .admittedRule5 := rule5_answer_value _ _ _ _ _ _ _

theorem admitted_route_split (W : OrdinaryWork) (T S : Tree) (c : Candidate) (q : Nat) :
 (admittedRouteSource W T S c q).work=(admittedRouteSource (fun _ _ _=>0) T S c q).work+
 queryWork W (calls (actualCallback q) W T S c.a c.b q) := rule5_answer_split _ _ _ _ _ _ _

theorem admitted_route_bound {T S : Tree} {c d : Candidate} (q N Q L : Nat)
 (hp:DepthOne.proper T S=true)
 (forward:CherryBranching.select T S=some (.hard2,c))
 (reverse:CherryBranching.select S T=some (.hard2,d))
 (noT:Rule4.select T S=none) (noS:Rule4.select S T=none)
 (route:(hard2FrontMeter T S c q).value=.admittedRule5) (domain:InputDomain T S q N Q L) :
 ((admittedRouteSource (fun _ _ _=>0) T S c q).work:Rat)≤(C5 N Q L:Rat)*(233/100:Rat)^q := by
 have ad:=actual_admitted_route q hp forward reverse noT noS route
 have ch:CherryAt T c.parent c.a c.b:=(selected_actual forward).1
 simpa only [admittedRouteSource,Rule5ActualTrace.base] using actual_rule5_bound ch ad q N Q L domain

theorem actual_rule5_calls_native (W : OrdinaryWork) (T S : Tree) (a b q : Nat) :
 calls (actualCallback q) W T S a b q=
 Rule5ActualTrace.queries (actualCallback q) (Rule5ActualTrace.dispatchTrace (actualCallback q) T S a b q).calls :=
 dispatch_calls_native _ _ _ _ _ _ _ _ _

theorem actual_rule5_query_domain (W : OrdinaryWork) {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch:CherryAt T i a b) (ad:admitted T S a b=true) (q : Nat) {p : Tree×Tree} {r : Nat}
 (mem:(p,r)∈calls (actualCallback q) W T S a b q) :
 r<q ∧ DepthOne.proper p.1 p.2=true ∧ (leaves p.1).length≤(leaves T).length ∧ (leaves p.2).length≤(leaves T).length :=
 dispatch_query_domain _ _ _ _ ch ad q mem
end Universal233.Rule5ClosedSource
