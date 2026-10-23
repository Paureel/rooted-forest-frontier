import OutputMass
import CoreCover
namespace Universal233.BothBadGrouped
open RMAF CoreProgram SourceCoverage PairAssembly BinaryCheap
open ForestState ForestGroups RestrictionBridge PaidQueries GroupedFullQuery
open VertexGeometry BinaryExchange

structure Evaluation where
 candidates : List Forest
 queries : List (Problem × Nat)

/-- One actual per-output result supplies BOTH its forest and its query trace. -/
def evaluate (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat) : List Output → Evaluation
 | [] => ⟨[],[]⟩
 | o::os =>
   let r := runOutput actual T S A B C q o
   let tail := evaluate actual T S A B C q os
   ⟨r.answer?.toList++tail.candidates,r.trace++tail.queries⟩

theorem evaluate_candidates (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat) (xs : List Output) :
 (evaluate actual T S A B C q xs).candidates=xs.filterMap (answerFor actual T S A B C q) := by
 induction xs with
 | nil => rfl
 | cons o os ih =>
   cases h : (runOutput actual T S A B C q o).answer? <;>
     simp [evaluate,List.filterMap_cons,answerFor,h,ih]

theorem evaluate_queries (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat) (xs : List Output) :
 (evaluate actual T S A B C q xs).queries=allTrace actual T S A B C q xs := by
 induction xs with
 | nil => rfl
 | cons o os ih => simp [evaluate,allTrace,traceFor,ih]

def accepted (T S : Tree) (q : Nat) (F : Forest) : Bool := agreement T S F && decide (F.length-1≤q)
structure PairExecution where
 answer : Option Forest
 queries : List (Problem × Nat)

def executePair (actual : Ordinary) (T S : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) : PairExecution :=
 let r := evaluate actual T S A B C q (BothBad.outputs S A B (PairGeometry.descendants T edge.2) q)
 ⟨best List.length (accepted T S q) r.candidates,r.queries⟩

theorem pair_sound (actual : Ordinary) (T S : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) (H : Forest)
 (answer : (executePair actual T S A B C edge q).answer=some H) :
 agreement T S H=true ∧ H.length-1≤q := by
 have h := (best_spec List.length (accepted T S q) _ H answer).2.1
 simpa [accepted] using h

theorem pair_complete (actual : Ordinary) (q : Nat) (below : BelowIH q actual)
 (S T : Tree) (A B C : List Nat) (edge : RMAF.Vertex × RMAF.Vertex)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup) (same : ∀ x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (he : pairwiseEmbeddings S [A,B,C]=true)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false)
 (badC : restrictionAgrees S T C=false) (hac : Disj T A C) (hbc : Disj T B C)
 (selected : PairGeometry.choose T A B=some (.edge edge)) (F : Forest)
 (ha : agreement T S F=true) (href : RefinesBlocks F [A,B,C]) (budget : F.length-1≤q) :
 ∃ H,(executePair actual T S A B C edge q).answer=some H ∧ H.length≤F.length := by
 obtain ⟨o,ho,witness⟩ := BothBad.selected_binary_core_cover S T A B C edge F hs ht hp selected ha href q budget
 have refP : RestrictionBridge.Refines F o.partition := by
   intro K hK
   obtain ⟨U,hU,sub⟩ := witness.1 K hK
   exact ⟨U,hU,fun x hx => sub x hx⟩
 obtain ⟨G,hG,len⟩ := fixed_output_complete actual q below S T A B C _ o hs ht same hp he badA badB badC hac hbc ho F ha refP budget
 have cand : G∈(evaluate actual T S A B C q (BothBad.outputs S A B (PairGeometry.descendants T edge.2) q)).candidates := by
   rw [evaluate_candidates]
   exact List.mem_filterMap.2 ⟨o,ho,hG⟩
 have valid := fixed_output_sound actual q below S T A B C _ o hs ht same hp he badA badB badC hac hbc ho G hG
 have acc : accepted T S q G=true := by simp [accepted,valid.1,valid.2.2.1]
 obtain ⟨H,hH⟩ := best_exists List.length (accepted T S q) _ G cand acc
 have least := (best_spec List.length (accepted T S q) _ H hH).2.2 G cand acc
 exact ⟨H,hH,Nat.le_trans least len⟩

theorem pair_minimum (actual : Ordinary) (q : Nat) (below : BelowIH q actual)
 (S T : Tree) (A B C : List Nat) (edge : RMAF.Vertex × RMAF.Vertex)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup) (same : ∀ x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (he : pairwiseEmbeddings S [A,B,C]=true)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false)
 (badC : restrictionAgrees S T C=false) (hac : Disj T A C) (hbc : Disj T B C)
 (selected : PairGeometry.choose T A B=some (.edge edge)) (H : Forest)
 (answer : (executePair actual T S A B C edge q).answer=some H) :
 ∀ F,agreement T S F=true → RefinesBlocks F [A,B,C] → H.length≤F.length := by
 have sound := pair_sound actual T S A B C edge q H answer
 intro F ha href
 by_cases budget : F.length-1≤q
 · obtain ⟨G,hG,len⟩ := pair_complete actual q below S T A B C edge hs ht same hp he badA badB badC hac hbc selected F ha href budget
   have eq : G=H := Option.some.inj (hG.symm.trans answer)
   simpa [eq] using len
 · omega

theorem pair_actual_mass (actual : Ordinary) (q : Nat) (S T : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex × RMAF.Vertex) (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀ x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (he : pairwiseEmbeddings S [A,B,C]=true)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false)
 (badC : restrictionAgrees S T C=false) (hac : Disj T A C) (hbc : Disj T B C)
 (selected : PairGeometry.choose T A B=some (.edge edge)) (c : Rat) (hc : 2≤c) :
 actualQueryMass c q ((executePair actual T S A B C edge q).queries.map Prod.snd)≤2*c^(-4:Int) := by
 change actualQueryMass c q ((evaluate actual T S A B C q _).queries.map Prod.snd)≤_
 rw [evaluate_queries]
 exact actual_pair_mass actual q S T A B C edge hs ht same hp he badA badB badC hac hbc selected c hc
end Universal233.BothBadGrouped
