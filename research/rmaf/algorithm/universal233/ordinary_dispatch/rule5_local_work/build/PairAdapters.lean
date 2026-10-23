import PairRefinement
import BothBadBinding
import PairExact
namespace OrdinaryDispatch.Hard2Dispatcher
open RMAF ForestState RestrictionBridge Universal233 Universal233.BothBad
abbrev Ordinary := Tree → Tree → Nat → Option (List (List Nat))
abbrev Forest := List (List Nat)
abbrev BelowIH (q : Nat) (actual : Ordinary) := ∀r,r<q→ForestMinCompletion.LocalOrdinaryIH r actual

def groupedExecution (r : BothBadGrouped.PairExecution) : Execution :=
 ⟨r.answer,r.queries.map (fun x=>⟨x.1.target,x.1.sources,x.2⟩)⟩

def badPair (actual : Ordinary) (T S : Tree) (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) : Execution :=
 if restrictionAgrees S T C then BothBadLocal.runPair actual S T A B C edge q
 else groupedExecution (BothBadGrouped.executePair actual T S A B C edge q)

theorem groupedExecution_mass (c : Rat) (q : Nat) (r : BothBadGrouped.PairExecution) :
 traceMass c q (groupedExecution r).calls=PaidQueries.actualQueryMass c q (r.queries.map Prod.snd) := by
 simp [groupedExecution,traceMass,List.map_map,Function.comp_def]

theorem refines_blocks {F P : Forest} (refine : Refines F P) : SourceCoverage.RefinesBlocks F P := by
 intro K hK
 obtain ⟨U,hU,sub⟩ := refine K hK
 exact ⟨U,hU,fun x hx=>sub hx⟩

theorem badPair_sound (actual : Ordinary) (T S : Tree) (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex)
 (q : Nat) (F : Forest) (answer : (badPair actual T S A B C edge q).answer=some F) :
 agreement T S F=true ∧ F.length-1≤q := by
 unfold badPair at answer
 split at answer
 · exact BothBadLocal.solvePair_sound actual S T A B C edge q F answer
 · exact BothBadGrouped.pair_sound actual T S A B C edge q F answer

theorem badPair_complete (actual : Ordinary) (T S : Tree) (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat)
 (below : BelowIH q actual) (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (es : pairwiseEmbeddings S [A,B,C]=true)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false)
 (ac : BinaryExchange.Disj T A C) (bc : BinaryExchange.Disj T B C)
 (selected : PairGeometry.choose T A B=some (.edge edge))
 (F : Forest) (hf : agreement T S F=true) (href : Refines F [A,B,C]) (budget : F.length-1≤q) :
 ∃G,(badPair actual T S A B C edge q).answer=some G ∧ G.length≤F.length := by
 cases goodC : restrictionAgrees S T C with
 | false =>
  obtain ⟨G,hG,min⟩ := BothBadGrouped.pair_complete actual q below S T A B C edge hs ht same hp es
   badA badB goodC ac bc selected F hf (refines_blocks href) budget
  exact ⟨G,by simpa [badPair,goodC,groupedExecution] using hG,min⟩
 | true =>
  obtain ⟨G,hG,_,_,min⟩ := BothBadLocal.solvePair_conditional_cover actual S T A B C edge q F hs ht
   (fun x=>(same x).symm) hp es badA badB goodC selected ac bc hf (refines_blocks href) budget below
  exact ⟨G,by simpa [badPair,goodC] using hG,min⟩

theorem badPair_mass (actual : Ordinary) (T S : Tree) (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (es : pairwiseEmbeddings S [A,B,C]=true)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false)
 (ac : BinaryExchange.Disj T A C) (bc : BinaryExchange.Disj T B C)
 (selected : PairGeometry.choose T A B=some (.edge edge))
 (c : Rat) (hc : 2≤c) (upper : c≤3) :
 traceMass c q (badPair actual T S A B C edge q).calls≤4*c^(-4 : Int) := by
 cases goodC : restrictionAgrees S T C with
 | false =>
  have h := BothBadGrouped.pair_actual_mass actual q S T A B C edge hs ht same hp es badA badB goodC ac bc selected c hc
  have nonneg : (0 : Rat)≤c^(-4 : Int) := Rat.le_of_lt (Rat.zpow_pos (by grind : 0<c))
  have factor : (2 : Rat)≤4 := by decide
  have high := Rat.mul_le_mul_of_nonneg_right factor nonneg
  exact Rat.le_trans (by simpa [badPair,goodC,groupedExecution_mass] using h) high
 | true =>
  have h := BothBadLocal.solvePair_trace_mass actual S T A B C edge q c hc upper hs ht
   (fun x=>(same x).symm) hp es badA badB goodC selected ac bc
  simpa [badPair,goodC] using h
end OrdinaryDispatch.Hard2Dispatcher
