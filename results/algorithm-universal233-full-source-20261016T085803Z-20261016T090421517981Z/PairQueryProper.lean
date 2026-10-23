import QueryProperBase
namespace OrdinaryDispatch.WorkIntegration
open RMAF ForestState ForestGroups RestrictionBridge Universal233 Universal233.BothBad Universal233.PaidQueries
open Universal233.CherryBranching Universal233.Hard2Overlap

theorem grouped_output_query_proper (actual : Ordinary) (T S : Tree) (A B C : List Nat)
 (q : Nat) (o : CoreProgram.Output) (p : GroupedFullQuery.Problem) (r : Nat)
 (mem : (p,r)∈BothBadGrouped.traceFor actual T S A B C q o) : proper p.target p.sources=true := by
 unfold BothBadGrouped.traceFor BothBadGrouped.runOutput at mem
 split at mem
 · split at mem
   · simp [BothBadGrouped.OutputResult.trace] at mem
   · rename_i js prep
     change (p,r)∈GroupedFullQuery.fullTrace actual (q-o.sourceCuts.length) js at mem
     exact full_group_query_proper actual (some T) _ [A++B,C] _ js prep p r mem
 · simp [BothBadGrouped.OutputResult.trace] at mem

theorem grouped_pair_query_proper (actual : Ordinary) (T S : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) (p : GroupedFullQuery.Problem) (r : Nat)
 (mem : (p,r)∈(BothBadGrouped.executePair actual T S A B C edge q).queries) : proper p.target p.sources=true := by
 change (p,r)∈(BothBadGrouped.evaluate actual T S A B C q _).queries at mem
 rw [BothBadGrouped.evaluate_queries] at mem
 obtain ⟨o,ho,query⟩ := List.mem_flatMap.1 mem
 exact grouped_output_query_proper actual T S A B C q o p r query

theorem grouped_execution_query_proper (actual : Ordinary) (T S : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) (call : Call)
 (mem : call∈(Hard2Dispatcher.groupedExecution (BothBadGrouped.executePair actual T S A B C edge q)).calls) :
 proper call.target call.sources=true := by
 obtain ⟨pb,hpb,eq⟩ := List.mem_map.1 mem
 subst call
 exact grouped_pair_query_proper actual T S A B C edge q pb.1 pb.2 hpb

theorem hard_paid_query_proper (actual : Ordinary) {T S : Tree} {c : Candidate} (q : Nat) (out : Result)
 (proper0 : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (call : Call) (mem : call∈(Hard2PaidLocal.runHardPaid actual T S q c out).calls) :
 proper call.target call.sources=true := by
 obtain ⟨o,ho,facts,target,sources,_⟩ := Hard2PaidLocal.actual_paid_full_source_call out q actual proper0 hard call mem
 have p := OrdinaryPriorityBridge.proper_parts proper0
 rw [target,sources]
 exact OutputState.sourceForest_proper T S o.partition p.1 p.2.1 (fun _=>p.2.2.mem_iff) facts.1

theorem good_pair_query_proper (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup) (same : ∀x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true)
 (ac : BinaryExchange.Disj T A C) (bc : BinaryExchange.Disj T B C)
 (call : Call) (mem : call∈(GoodPairDP.runPair actual T S A B C q).calls) : proper call.target call.sources=true := by
 have ref : SourceCoverage.RefinesBlocks [A,B,C] [A,B,C] := by intro K hK;exact ⟨K,hK,fun _ hx=>hx⟩
 have geometry := GroupedFullQuery.abc_geometry T S [A,B,C] A B C hs ht same hp hp ref ac bc
 have cp := local_proper (some T) (OutputState.sourceForest S [A,B,C]) [A++B,C]
  geometry.1 geometry.2.1 geometry.2.2.1 C (by simp)
 unfold GoodPairDP.runPair at mem
 split at mem
 · try dsimp only at mem
   split at mem
   · simp at mem
   · try dsimp only at mem
     split at mem
     · have eq := List.mem_singleton.1 mem
       subst call
       exact cp
     · simp at mem
 · simp at mem
end OrdinaryDispatch.WorkIntegration
