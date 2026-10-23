import PairQueryProper
namespace OrdinaryDispatch.WorkIntegration
open RMAF ForestState ForestGroups RestrictionBridge Universal233 Universal233.BothBad Universal233.PaidQueries

def ModeSafe (P : List (List Nat)) : Mode→Prop
 | .ordinary => True
 | .full => True
 | .retained _ residual _ _ => residual∈P

theorem entries_mode_safe (P : List (List Nat)) (q : Nat) (mode : Mode) (xs : List CoreProgram.Output)
 (safe : ModeSafe P mode) (e : Entry) (mem : e∈entries q mode xs) : ModeSafe P e.mode := by
 rw [(entries_sound q mode xs e mem).2.1]
 exact safe

theorem cheap_plan_mode_safe (P : List (List Nat)) (S T : Tree) (A B C D : List Nat) (q : Nat)
 (cheap opposite : List CoreProgram.Output) (member : B∈P) (e : Entry)
 (mem : e∈cheapPlan S T A B C D q cheap opposite) : ModeSafe P e.mode := by
 unfold cheapPlan at mem
 try dsimp only at mem
 split at mem
 · split at mem
   · simp at mem
   · rcases List.mem_append.1 mem with ordinary|retained
     · exact entries_mode_safe P q .ordinary cheap True.intro e ordinary
     · exact entries_mode_safe P q (.retained A B C _) opposite member e retained
 · rcases List.mem_append.1 mem with ordinary|full
   · exact entries_mode_safe P q .ordinary cheap True.intro e ordinary
   · exact entries_mode_safe P q .full opposite True.intro e full

theorem plan_mode_safe (S T : Tree) (A B C D : List Nat) (q : Nat) (e : Entry)
 (mem : e∈plan S T A B C D q) : ModeSafe [A,B,C] e.mode := by
 unfold plan at mem
 split at mem
 · simp at mem
 · try dsimp only at mem
   split at mem
   · split at mem
     · exact entries_mode_safe [A,B,C] q .full _ True.intro e mem
     · exact cheap_plan_mode_safe [A,B,C] S T B A C D q _ _ (by simp) e mem
   · exact cheap_plan_mode_safe [A,B,C] S T A B C D q _ _ (by simp) e mem

theorem dispatch_query_proper (solve : ForestSolver) (T S : Tree) (P : List (List Nat)) (e : Entry)
 (state : proper (some T) (OutputState.sourceForest S e.output.partition)=true)
 (part : partitionCheck (labels (some T)) P=true)
 (own : Owns (OutputState.sourceForest S e.output.partition) P) (safe : ModeSafe P e.mode)
 (call : Call) (mem : call∈(dispatch solve T S e).calls) : proper call.target call.sources=true := by
 cases e with
 | mk o mode b =>
  cases mode with
  | ordinary => exact ordinary_execution_queries_proper solve T S _ b call mem
  | full =>
   have eq : call=⟨some T,OutputState.sourceForest S o.partition,b⟩ := by simpa [dispatch] using mem
   subst call;exact state
  | retained X Y Z known =>
   have eq : call=⟨localTarget (some T) Y,owned (OutputState.sourceForest S o.partition) Y,b⟩ := by simpa [dispatch] using mem
   subst call
   exact local_proper (some T) _ P state part own Y safe

theorem both_bad_local_query_proper (actual : Ordinary) (S T : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup) (same : ∀x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (es : pairwiseEmbeddings S [A,B,C]=true)
 (selected : PairGeometry.choose T A B=some (.edge edge))
 (call : Call) (mem : call∈(BothBadLocal.runPair actual S T A B C edge q).calls) : proper call.target call.sources=true := by
 change call∈(execute (GenericForest.solve actual) T S q (plan S T A B C (PairGeometry.descendants T edge.2) q)).calls at mem
 rw [execute_calls] at mem
 obtain ⟨e,he,query⟩ := List.mem_flatMap.1 mem
 have emitted := plan_sources S T A B C edge hs ht (fun x hx=>(same x).2 hx) hp selected q e he
 have facts := BothBadGrouped.outputs_facts S A B C _ q e.output hp es emitted
 have state := OutputState.sourceForest_proper T S e.output.partition ht hs same facts.part
 have part : partitionCheck (labels (some T)) [A,B,C]=true :=
  (partition_labels_congr _ _ _ same).2 hp
 have own := OutputState.original_source_ownership S e.output.partition [A,B,C] hs facts.part facts.refines
 exact dispatch_query_proper (GenericForest.solve actual) T S [A,B,C] e state part own
  (plan_mode_safe S T A B C _ q e he) call query
end OrdinaryDispatch.WorkIntegration
