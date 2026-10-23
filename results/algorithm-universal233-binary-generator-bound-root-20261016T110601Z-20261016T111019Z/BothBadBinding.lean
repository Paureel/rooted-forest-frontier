import OrdinaryLocal
namespace Universal233.BothBadLocal
open RMAF CoreProgram ForestState RestrictionBridge SourceCoverage BothBad VertexGeometry BinaryExchange

/-- The literal completed runtime, with the actual ordinary callback only. -/
def runPair (actual : Ordinary) (S T : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) : Execution :=
 BothBad.solvePair (GenericForest.solve actual) S T A B C edge q

theorem runPair_literal (actual : Ordinary) (S T : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) :
 runPair actual S T A B C edge q=BothBad.solvePair (GenericForest.solve actual) S T A B C edge q := rfl

theorem solvePair_answer_congr_below (f g : ForestSolver) (S T : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat)
 (equal : ∀t ss b,b<q → f t ss b=g t ss b)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (hl : ∀x,x∈leaves S → x∈leaves T)
 (hp : partitionCheck (leaves S) [A,B,C]=true)
 (selected : PairGeometry.choose T A B=some (.edge edge)) :
 (BothBad.solvePair f S T A B C edge q).answer=(BothBad.solvePair g S T A B C edge q).answer := by
 apply execute_answer_congr_entries
 intro e mem
 have bound := plan_entry_budget_drop S T A B C edge q e hs ht hl hp selected mem
 exact dispatch_answer_congr_at f g e.budget
  (fun t ss b hb=>equal t ss b (by omega)) T S e (Nat.le_refl _)

theorem solvePair_sound (actual : Ordinary) (S T : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) (H : Forest)
 (answer : (runPair actual S T A B C edge q).answer=some H) :
 agreement T S H=true ∧ H.length-1≤q :=
 execute_sound (GenericForest.solve actual) T S q _ H answer

theorem solvePair_conditional_cover (actual : Ordinary) (S T : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) (F : Forest)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀x,x∈leaves S ↔ x∈leaves T)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (source : pairwiseEmbeddings S [A,B,C]=true)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false)
 (goodC : restrictionAgrees S T C=true)
 (selected : PairGeometry.choose T A B=some (.edge edge))
 (ac : Disj T A C) (bc : Disj T B C)
 (agree : agreement T S F=true) (refine : SourceCoverage.RefinesBlocks F [A,B,C])
 (budget : F.length-1≤q) (IH : BelowIH q actual) :
 ∃H,(runPair actual S T A B C edge q).answer=some H ∧
 agreement T S H=true ∧ H.length-1≤q ∧ H.length≤F.length := by
 obtain ⟨completed,global,equal⟩ := below_ordinary_extension IH
 have exactness := completed_forest_exact completed global
 obtain ⟨H,answer,hAF,hcost,len⟩ := BothBad.solvePair_conditional_cover (GenericForest.solve completed)
  S T A B C edge q F hs ht same hp source badA badB goodC selected ac bc agree refine budget exactness
 have answers := solvePair_answer_congr_below (GenericForest.solve completed) (GenericForest.solve actual)
  S T A B C edge q (forest_programs_congr_below completed actual q equal) hs ht (fun x hx=>(same x).1 hx) hp selected
 exact ⟨H,answers.symm.trans answer,hAF,hcost,len⟩

/-- Minimum among the original parent-refining agreements. The surrounding
hard2 dispatcher retains its two endpoint alternatives. -/
theorem solvePair_minimum (actual : Ordinary) (S T : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) (H : Forest)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀x,x∈leaves S ↔ x∈leaves T)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (source : pairwiseEmbeddings S [A,B,C]=true)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false)
 (goodC : restrictionAgrees S T C=true)
 (selected : PairGeometry.choose T A B=some (.edge edge))
 (ac : Disj T A C) (bc : Disj T B C) (IH : BelowIH q actual)
 (answer : (runPair actual S T A B C edge q).answer=some H) :
 agreement T S H=true ∧ H.length-1≤q ∧
 ∀F,agreement T S F=true → SourceCoverage.RefinesBlocks F [A,B,C] → H.length≤F.length := by
 obtain ⟨hAF,hcost⟩ := solvePair_sound actual S T A B C edge q H answer
 refine ⟨hAF,hcost,?_⟩
 intro F agree refine
 by_cases budget : F.length-1≤q
 · obtain ⟨G,hG,_,_,len⟩ := solvePair_conditional_cover actual S T A B C edge q F hs ht same hp source
    badA badB goodC selected ac bc agree refine budget IH
   have eq : G=H := Option.some.inj (hG.symm.trans answer)
   simpa [eq] using len
 · omega

theorem solvePair_calls_strict (actual : Ordinary) (S T : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) (call : Call)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (hl : ∀x,x∈leaves S → x∈leaves T)
 (hp : partitionCheck (leaves S) [A,B,C]=true)
 (selected : PairGeometry.choose T A B=some (.edge edge))
 (mem : call∈(runPair actual S T A B C edge q).calls) : call.budget+3≤q ∧ call.budget<q := by
 have bound := BothBad.solvePair_calls_drop (GenericForest.solve actual) S T A B C edge q call hs ht hl hp selected mem
 exact ⟨bound,by omega⟩

theorem solvePair_trace_mass (actual : Ordinary) (S T : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) (c : Rat) (base : 2≤c) (upper : c≤3)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀x,x∈leaves S ↔ x∈leaves T)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (source : pairwiseEmbeddings S [A,B,C]=true)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false)
 (goodC : restrictionAgrees S T C=true)
 (selected : PairGeometry.choose T A B=some (.edge edge))
 (ac : Disj T A C) (bc : Disj T B C) :
 traceMass c q (runPair actual S T A B C edge q).calls≤4*c^(-4 : Int) :=
 BothBad.solvePair_actual_mass (GenericForest.solve actual) S T A B C edge q c base upper hs ht same hp source badA badB goodC selected ac bc
end Universal233.BothBadLocal
