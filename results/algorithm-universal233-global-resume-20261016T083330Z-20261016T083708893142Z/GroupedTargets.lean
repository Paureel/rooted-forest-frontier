import TargetBounds
namespace OrdinaryDispatch.Hard2Size
open RMAF ForestState ForestGroups RestrictionBridge Universal233 Universal233.BothBad
open Universal233.PaidQueries Universal233.GroupedFullQuery

theorem fullTrace_target_bound (actual : Ordinary) (T : Tree) (ss : List Tree) (Q : List (List Nat))
 (q : Nat) (js : List (Job Problem Forest))
 (prep : prepare (groupProblems (some T) ss Q)=some js)
 (p : Problem) (r : Nat) (mem : (p,r)∈fullTrace actual q js) : TargetBound T p.target := by
 have hard := fullTrace_jobs actual q js p r mem
 have names := (prepare_spec _ _ prep).1
 have pMem : p∈groupProblems (some T) ss Q := by
  rw [←names]
  exact List.mem_map.2 ⟨Job.hard p,hard,rfl⟩
 obtain ⟨U,hU,eq⟩ := List.mem_map.1 pMem
 rw [←eq]
 exact local_target_bound T U

theorem output_trace_target_bound (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat)
 (o : CoreProgram.Output) (p : Problem) (r : Nat)
 (mem : (p,r)∈BothBadGrouped.traceFor actual T S A B C q o) : TargetBound T p.target := by
 unfold BothBadGrouped.traceFor BothBadGrouped.runOutput at mem
 split at mem
 · split at mem
   · simp [BothBadGrouped.OutputResult.trace] at mem
   · rename_i js prep
     change (p,r)∈fullTrace actual (q-o.sourceCuts.length) js at mem
     exact fullTrace_target_bound actual T _ [A++B,C] _ js prep p r mem
 · simp [BothBadGrouped.OutputResult.trace] at mem

theorem grouped_pair_target_bound (actual : Ordinary) (T S : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) (p : Problem) (r : Nat)
 (mem : (p,r)∈(BothBadGrouped.executePair actual T S A B C edge q).queries) : TargetBound T p.target := by
 change (p,r)∈(BothBadGrouped.evaluate actual T S A B C q _).queries at mem
 rw [BothBadGrouped.evaluate_queries] at mem
 obtain ⟨o,ho,query⟩ := List.mem_flatMap.1 mem
 exact output_trace_target_bound actual T S A B C q o p r query

theorem grouped_execution_target_bound (actual : Ordinary) (T S : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) (call : Call)
 (mem : call∈(OrdinaryDispatch.Hard2Dispatcher.groupedExecution
 (BothBadGrouped.executePair actual T S A B C edge q)).calls) : TargetBound T call.target := by
 obtain ⟨pb,hpb,eq⟩ := List.mem_map.1 mem
 subst call
 exact grouped_pair_target_bound actual T S A B C edge q pb.1 pb.2 hpb
end OrdinaryDispatch.Hard2Size
