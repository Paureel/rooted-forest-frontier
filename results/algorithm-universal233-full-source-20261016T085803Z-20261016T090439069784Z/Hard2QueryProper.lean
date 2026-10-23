import ModeQueryProper
namespace OrdinaryDispatch.WorkIntegration
open RMAF ForestState ForestGroups RestrictionBridge Universal233 Universal233.BothBad Universal233.PaidQueries
open Universal233.CherryBranching Universal233.Hard2Overlap Universal233.PaidAssembly
open OrdinaryDispatch.Hard2Dispatcher

theorem badPair_query_proper (actual : Ordinary) (T S : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup) (same : ∀x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (es : pairwiseEmbeddings S [A,B,C]=true)
 (selected : PairGeometry.choose T A B=some (.edge edge))
 (call : Call) (mem : call∈(badPair actual T S A B C edge q).calls) : proper call.target call.sources=true := by
 unfold badPair at mem
 split at mem
 · exact both_bad_local_query_proper actual S T A B C edge q hs ht same hp es selected call mem
 · exact grouped_execution_query_proper actual T S A B C edge q call mem

theorem paidCase_query_proper (actual : Ordinary) {T S : Tree} {c : Candidate} {q : Nat} {out : Result}
 (proper0 : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (selected : runHard2 T S c=some out) (call : Call)
 (mem : call∈(paidCase actual T S c q out).calls) : proper call.target call.sources=true := by
 obtain ⟨p,r,cuts,hcuts,graph,hp,es,partEq⟩ := actual_source_inputs proper0 hard
 have basic := OrdinaryPriorityBridge.proper_parts proper0
 have ht := basic.1
 have hs := basic.2.1
 have same : ∀x,x∈leaves T ↔ x∈leaves S := fun _=>basic.2.2.mem_iff
 have hl : ∀x,x∈leaves S→x∈leaves T := fun x hx=>(same x).2 hx
 have raw : Hard2Overlap.select T (leftParent S p) (rightParent S r) (rootParent S p r)=some out := by
  simpa only [runHard2,cuts] using selected
 cases out with
 | disjoint => exact hard_paid_query_proper actual q _ proper0 hard call (by simpa [paidCase,cuts] using mem)
 | clique v => exact hard_paid_query_proper actual q _ proper0 hard call (by simpa [paidCase,cuts] using mem)
 | four o v w => exact hard_paid_query_proper actual q _ proper0 hard call (by simpa [paidCase,cuts] using mem)
 | diagonal o v w => exact hard_paid_query_proper actual q _ proper0 hard call (by simpa [paidCase,cuts] using mem)
 | pair o choice =>
  cases choice with
  | vertex v => exact hard_paid_query_proper actual q _ proper0 hard call (by simpa [paidCase,cuts] using mem)
  | edge edge =>
   let A := first o (leftParent S p) (rightParent S r) (rootParent S p r)
   let B := second o (leftParent S p) (rightParent S r) (rootParent S p r)
   let C := third o (leftParent S p) (rightParent S r) (rootParent S p r)
   obtain ⟨pp,pe,ne,pairProper,chosen,valid,other⟩ := selected_pair_guards ht hl hp es raw
   have guards := select_sound ht hl hp raw
   have ac : BinaryExchange.Disj T A C := FreshPairReview.actual_clear_disj T _ _ guards.1
   have bc : BinaryExchange.Disj T B C := FreshPairReview.actual_clear_disj T _ _ guards.2.1
   simp only [paidCase,cuts] at mem
   change call∈(if (restrictionAgrees S T A && restrictionAgrees S T B)=true then GoodPairDP.runPair actual T S A B C q
    else if (restrictionAgrees S T A || restrictionAgrees S T B)=true then Hard2PaidLocal.runHardPaid actual T S q c (.pair o (.edge edge))
    else badPair actual T S A B C edge q).calls at mem
   split at mem
   · exact good_pair_query_proper actual T S A B C q hs ht same pp ac bc call mem
   · split at mem
     · exact hard_paid_query_proper actual q _ proper0 hard call mem
     · exact badPair_query_proper actual T S A B C edge q hs ht same pp pe chosen call mem

theorem unit_query_proper {T S : Tree} {c : Candidate} (q : Nat)
 (proper0 : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (call : Call) (mem : call∈Hard2Combine.unitCalls S T c.a c.b q) : proper call.target call.sources=true := by
 have basic := OrdinaryPriorityBridge.proper_parts proper0
 have same : ∀x,x∈leaves T ↔ x∈leaves S := fun _=>basic.2.2.mem_iff
 have cherry := (selected_actual hard).1
 obtain ⟨child,hchild,hm⟩ := List.mem_filterMap.1 mem
 obtain ⟨r,hr,eq⟩ := Option.map_eq_some_iff.1 hm
 have cases : child=singletonChild S c.a ∨ child=singletonChild S c.b := by simpa using hchild
 have member : child∈branches S c.a c.b := by rcases cases with rfl|rfl <;> simp [branches]
 obtain ⟨part,emb,paid,material⟩ := three_children_literal basic.1 basic.2.1 same cherry child member
 have valid := OutputState.sourceForest_proper T S child.partition basic.1 basic.2.1 same part
 have ceq : call=⟨some T,child.sourceForest,r⟩ := eq.symm
 subst call
 simpa only [material] using valid

theorem combined_queries_proper (actual : Ordinary) {T S : Tree} {c : Candidate} {q : Nat} {out : Result}
 (proper0 : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (selected : runHard2 T S c=some out) (call : Call)
 (mem : call∈(Hard2Combine.combine actual T S c.a c.b q (paidCase actual T S c q out)).calls) : proper call.target call.sources=true := by
 change call∈Hard2Combine.unitCalls S T c.a c.b q++(paidCase actual T S c q out).calls at mem
 rcases List.mem_append.1 mem with unit|paid
 · exact unit_query_proper q proper0 hard call unit
 · exact paidCase_query_proper actual proper0 hard selected call paid

theorem disjoint_queries_proper (actual : Ordinary) {T S : Tree} {c : Candidate} (q : Nat)
 (proper0 : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (call : Call) (mem : call∈(Hard2Trace.disjointExecution actual T S c.a c.b q).calls) : proper call.target call.sources=true := by
 change call∈Hard2Combine.unitCalls S T c.a c.b q++(DisjointParents.query actual T S (pendantPartition S c.a c.b) q).calls at mem
 rcases List.mem_append.1 mem with unit|paid
 · exact unit_query_proper q proper0 hard call unit
 · unfold DisjointParents.query at paid
   split at paid
   · exact ordinary_execution_queries_proper (GenericForest.solve actual) T S _ _ call paid
   · simp at paid
end OrdinaryDispatch.WorkIntegration
