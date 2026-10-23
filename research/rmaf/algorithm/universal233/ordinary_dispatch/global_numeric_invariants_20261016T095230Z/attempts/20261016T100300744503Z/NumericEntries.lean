import NumericStateBounds
namespace OrdinaryDispatch.GlobalNumeric
open RMAF ForestState Universal233 Universal233.CoreWork Universal233.CherryBranching Universal233.BothBad
open Universal233.Hard2Overlap
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open Rule5Local Rule5Classification Rule5FinalClassification Rule5SourceOrientation Rule5OrdinaryDispatch Rule5ActualTrace
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.Hard2Dispatcher

/-- Conclusion-only semantic entry contract; no constructor assumes this record. -/
def ForestCaps (N M Q : Nat) (call : Call) : Prop :=
 proper call.target call.sources=true ∧ (labels call.target).length≤N ∧ call.budget≤Q ∧
 ∀x,x∈labels call.target→x≤M

def jobCall (j : ForestJob) : Call := ⟨j.target,j.sources,j.residual⟩
def childCalls (T : Tree) (q : Nat) (cs : List Child) : List Call := (forestJobs T q cs).map jobCall

theorem child_entry_caps (T : Tree) (q N M : Nat) (cs : List Child)
 (valid : ∀c,c∈cs→proper (some T) c.sourceForest=true)
 (sz : (leaves T).length≤N) (cap : TreeCap M T) (call : Call) (mem : call∈childCalls T q cs) : ForestCaps N M q call := by
 obtain ⟨j,hj,rfl⟩:=List.mem_map.1 mem
 have facts:=literal_job_binding hj
 have hp : proper j.target j.sources=true := by rw [facts.2.1,facts.2.2.1];exact valid j.child facts.1
 have residual : j.residual≤q := by
  have rem:=facts.2.2.2
  unfold remaining at rem
  split at rem
  · have eq:=(Option.some.inj rem).symm;omega
  · contradiction
 exact ⟨hp,by change (labels j.target).length≤N;rw [facts.2.1];exact sz,residual,
  by change ∀x,x∈labels j.target→x≤M;rw [facts.2.1];exact cap⟩

theorem rule4_entry_caps {T S : Tree} (s : Rule4.Choice T S) (q N M : Nat)
 (sz : (leaves T).length≤N) (cap : PairCap M T S) (call : Call) (mem : call∈rule4Calls s q) : ForestCaps N M q call := by
 have facts:=rule4_call_facts s q call mem
 refine ⟨facts.1,Nat.le_trans facts.2.1 sz,Nat.le_of_lt facts.2.2,?_⟩
 obtain ⟨b,hb,_,eq⟩:=affordableCalls_member (Rule4.branches s) Rule4.Branch.target Rule4.Branch.sourceForest Rule4.Branch.cost q call mem
 subst call
 simp only [Rule4.branches,List.mem_cons,List.not_mem_nil,or_false] at hb
 rcases hb with rfl|rfl|rfl
 · exact cap.1
 · exact cap.1
 · exact cap.2

theorem combined_entry_caps (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree} {c : Candidate}
 {q : Nat} {out : Hard2Overlap.Result} (hp : DepthOne.proper T S=true)
 (hard : CherryBranching.select T S=some (.hard2,c)) (selected : runHard2 T S c=some out)
 (N M : Nat) (sz : (leaves T).length≤N) (cap : TreeCap M T) (call : Call)
 (mem : call∈(Hard2Combine.combine actual T S c.a c.b q (paidCase actual T S c q out)).calls) : ForestCaps N M q call := by
 have target:=Hard2Size.combined_target_bound actual T S c q out call mem
 exact ⟨combined_queries_proper actual hp hard selected call mem,Nat.le_trans target.2 sz,
  Nat.le_of_lt (Hard2Trace.combined_calls_strict actual hp hard selected call mem),fun x hx=>cap x (target.1 x hx)⟩

theorem disjoint_entry_caps (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree} {c : Candidate}
 (q : Nat) (hp : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (N M : Nat) (sz : (leaves T).length≤N) (cap : TreeCap M T) (call : Call)
 (mem : call∈(Hard2Trace.disjointExecution actual T S c.a c.b q).calls) : ForestCaps N M q call := by
 have target:=Hard2Size.disjoint_target_bound actual T S c.a c.b q call mem
 exact ⟨disjoint_queries_proper actual q hp hard call mem,Nat.le_trans target.2 sz,
  Nat.le_of_lt (Hard2Trace.disjointExecution_strict actual q hp hard call mem),fun x hx=>cap x (target.1 x hx)⟩

/-- Literal hard fallbacks only: answered/refused full-state pretests and small
budgets do not call GenericForest.solve. Repeated entries are kept. -/
def currentForestCalls (j : Rule5PaidSelector.PaidRequest) : List Call :=
 match ForestPretest01.pretest01 (some j.target) j.sources with
 | .rejected => if j.residual≤1 then [] else [⟨some j.target,j.sources,j.residual⟩]
 | _ => []

def rule5ForestCalls (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree) (a b q : Nat) : List Call :=
 match (dispatchTrace actual T S a b q).calls with
 | .forestJobs jobs => jobs.map jobCall
 | .direct _ => []
 | .paidRequests jobs => jobs.flatMap currentForestCalls
 | .selectorRefused | .paidBuilderRefused => []

theorem paid_entry_caps (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree} {a b : Nat}
 {R : Rule5PaidSelector.SelectedPaid T S} (built : Rule5PaidSelector.buildSelected T S a b=some R)
 (q N M : Nat) (sz : (leaves T).length≤N ∧ (leaves S).length≤N) (cap : PairCap M T S)
 (j : Rule5PaidSelector.PaidRequest) (hj : j∈Rule5PaidSelector.requests R.geometry q) :
 ForestCaps N M q ⟨some j.target,j.sources,j.residual⟩ := by
 have binding:=second_request_binding built hj
 obtain ⟨c,hc,request⟩:=List.mem_filterMap.1 hj
 obtain ⟨aff,branch,target,sources,residual⟩:=Rule5PaidSelector.requestFor_binding request
 refine ⟨binding.2.2,?_,Nat.le_of_lt binding.1,?_⟩
 · change (leaves j.target).length≤N
   rw [target];unfold Rule5PaidSelector.opposite;split
   · exact sz.1
   · exact sz.2
 · change TreeCap M j.target
   rw [target];unfold Rule5PaidSelector.opposite;split
   · exact cap.1
   · exact cap.2

theorem rule5_entry_caps (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree}
 {i : RMAF.Vertex} {a b : Nat} (ch : CoreGraph.CherryAt T i a b) (ad : admitted T S a b=true)
 (q N M : Nat) (sz : (leaves T).length≤N ∧ (leaves S).length≤N) (cap : PairCap M T S)
 (call : Call) (mem : call∈rule5ForestCalls actual T S a b q) : ForestCaps N M q call := by
 obtain ⟨z,sel,_⟩:=final_classification_complete ch ad
 unfold rule5ForestCalls at mem
 rw [dispatchTrace,sel] at mem
 have forestArm (hm : call∈(forestJobs T q (selectedForestChildren S a b z)).map jobCall) : ForestCaps N M q call :=
  child_entry_caps T q N M _ (fun c hc=>selected_child_proper ch ad sel hc) sz.1 cap.1 call hm
 cases z with
 | «prefix» s => exact forestArm mem
 | remaining d z =>
  cases z with
  | first u v => exact forestArm mem
  | third u v => exact forestArm mem
  | one edge => simp only [selectedTrace] at mem;exact False.elim (List.not_mem_nil mem)
  | second u v =>
   cases built : Rule5PaidSelector.buildSelected T S a b with
   | none => simp [selectedTrace,built] at mem
   | some R =>
    simp only [selectedTrace,built] at mem
    change call∈(Rule5PaidSelector.requests R.geometry q).flatMap currentForestCalls at mem
    obtain ⟨j,hj,hcall⟩:=List.mem_flatMap.1 mem
    have facts:=paid_entry_caps actual built q N M sz cap j hj
    unfold currentForestCalls at hcall
    split at hcall
    · split at hcall
      · simp at hcall
      · have eq:call=⟨some j.target,j.sources,j.residual⟩:=List.mem_singleton.1 hcall
        rw [eq];exact facts
    · simp at hcall
    · simp at hcall
end OrdinaryDispatch.GlobalNumeric
