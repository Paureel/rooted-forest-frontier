import BadGroupedPair
namespace Universal233.BothBadGrouped
open RMAF CoreProgram SourceCoverage PairAssembly BinaryCheap
open ForestState ForestGroups RestrictionBridge PaidQueries GroupedFullQuery
open VertexGeometry BinaryExchange

/-- Returned candidates belong to the SAME original three-parent refinement
class used by the complete source-core cover. No desired class is assumed. -/
theorem pair_refines (actual : Ordinary) (q : Nat) (below : BelowIH q actual)
 (S T : Tree) (A B C : List Nat) (edge : RMAF.Vertex × RMAF.Vertex)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup) (same : ∀ x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (he : pairwiseEmbeddings S [A,B,C]=true)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false)
 (badC : restrictionAgrees S T C=false) (hac : Disj T A C) (hbc : Disj T B C)
 (H : Forest) (answer : (executePair actual T S A B C edge q).answer=some H) :
 RefinesBlocks H [A,B,C] := by
 have mem := (best_spec List.length (accepted T S q) _ H answer).1
 rw [evaluate_candidates] at mem
 obtain ⟨o,ho,hO⟩ := List.mem_filterMap.1 mem
 have sound := fixed_output_sound actual q below S T A B C _ o hs ht same hp he badA badB badC hac hbc ho H hO
 have f := outputs_facts S A B C _ q o hp he ho
 intro K hK
 obtain ⟨U,hU,sub⟩ := sound.2.1 K hK
 obtain ⟨V,hV,parent⟩ := f.refines U hU
 exact ⟨V,hV,fun x hx => parent x (sub hx)⟩

theorem pair_feasible_iff (actual : Ordinary) (q : Nat) (below : BelowIH q actual)
 (S T : Tree) (A B C : List Nat) (edge : RMAF.Vertex × RMAF.Vertex)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup) (same : ∀ x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (he : pairwiseEmbeddings S [A,B,C]=true)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false)
 (badC : restrictionAgrees S T C=false) (hac : Disj T A C) (hbc : Disj T B C)
 (selected : PairGeometry.choose T A B=some (.edge edge)) :
 (∃ H,(executePair actual T S A B C edge q).answer=some H) ↔
 ∃ F,agreement T S F=true ∧ RefinesBlocks F [A,B,C] ∧ F.length-1≤q := by
 constructor
 · rintro ⟨H,hH⟩
   have hsnd := pair_sound actual T S A B C edge q H hH
   exact ⟨H,hsnd.1,pair_refines actual q below S T A B C edge hs ht same hp he badA badB badC hac hbc H hH,hsnd.2⟩
 · rintro ⟨F,ha,ref,budget⟩
   obtain ⟨H,hH,_⟩ := pair_complete actual q below S T A B C edge hs ht same hp he badA badB badC hac hbc selected F ha ref budget
   exact ⟨H,hH⟩
end Universal233.BothBadGrouped
