import OutputGuards
namespace Universal233.BothBadGrouped
open RMAF CoreProgram SourceCoverage PairAssembly BinaryCheap
open ForestState ForestGroups RestrictionBridge PaidQueries GroupedFullQuery
open VertexGeometry BinaryExchange

inductive OutputResult where
 | unaffordable
 | refused
 | scheduled (receipt : MeterReceipt Problem Forest)

def jobsFor (T S : Tree) (A B C : List Nat) (o : Output) : Option (List (Job Problem Forest)) :=
 prepare (groupProblems (some T) (OutputState.sourceForest S o.partition) [A++B,C])

/-- Replaces the output's query by literal AB/C full-state jobs. Every original
source cut is paid, independently of the legacy Entry.mode or extra field. -/
def runOutput (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat) (o : Output) : OutputResult :=
 if o.sourceCuts.length≤q then
   match jobsFor T S A B C o with
   | none => .refused
   | some js => .scheduled (meterSchedule (callback actual) (fun _ _ => 0) (q-o.sourceCuts.length) js)
 else .unaffordable

def OutputResult.answer? : OutputResult → Option Forest
 | .scheduled r => r.value.answers.map (List.flatMap Prod.snd)
 | _ => none

def OutputResult.trace : OutputResult → List (Problem × Nat)
 | .scheduled r => r.queries
 | _ => []

def answerFor (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat) (o : Output) : Option Forest :=
 (runOutput actual T S A B C q o).answer?
def traceFor (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat) (o : Output) : List (Problem × Nat) :=
 (runOutput actual T S A B C q o).trace

theorem output_affordable (S : Tree) (A B D : List Nat) (q : Nat) (o : Output)
 (ho : o∈BothBad.outputs S A B D q) : o.sourceCuts.length≤q := by
 rcases List.mem_append.1 ho with ho|ho
 all_goals exact generate_output_budget S _ q o ho

theorem runOutput_binding (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat) (o : Output)
 (paid : o.sourceCuts.length≤q) (js : List (Job Problem Forest)) (prep : jobsFor T S A B C o=some js) :
 runOutput actual T S A B C q o=
   .scheduled (meterSchedule (callback actual) (fun _ _ => 0) (q-o.sourceCuts.length) js) := by
 simp [runOutput,paid,prep]

theorem fixed_output_sound (actual : Ordinary) (q : Nat) (below : BelowIH q actual)
 (S T : Tree) (A B C D : List Nat) (o : Output)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup) (same : ∀ x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (he : pairwiseEmbeddings S [A,B,C]=true)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false)
 (badC : restrictionAgrees S T C=false) (hac : Disj T A C) (hbc : Disj T B C)
 (ho : o∈BothBad.outputs S A B D q) (H : Forest)
 (answer : answerFor actual T S A B C q o=some H) :
 agreement T S H=true ∧ RestrictionBridge.Refines H o.partition ∧ H.length-1≤q ∧
 ∀ F,agreement T S F=true → RestrictionBridge.Refines F o.partition → H.length≤F.length := by
 obtain ⟨js,prep,bad,proper,part,own,cross,f⟩ := output_jobs S T A B C D q o hs ht same hp he badA badB badC hac hbc ho
 have paid := output_affordable S A B D q o ho
 have binding := runOutput_binding actual T S A B C q o paid js prep
 have ah : (schedule (callback actual) (q-o.sourceCuts.length) js).answers.map (List.flatMap Prod.snd)=some H := by
   simpa [answerFor,binding,OutputResult.answer?,meterSchedule_value] using answer
 cases result : (schedule (callback actual) (q-o.sourceCuts.length) js).answers with
 | none => simp [result] at ah
 | some xs =>
   have eq : xs.flatMap Prod.snd=H := by simpa [result] using ah
   have belowb : BelowIH (q-o.sourceCuts.length) actual :=
     fun r hr => below r (Nat.lt_of_lt_of_le hr (Nat.sub_le _ _))
   obtain ⟨valid,costs,budget,least⟩ := grouped_sound actual _ belowb (some T) _ [A++B,C] js prep bad proper part own cross xs result
   rw [eq] at valid costs budget least
   obtain ⟨orig,ref⟩ := OutputState.state_to_original T S o.partition H hs same f.part f.source valid
   have fullcost := OutputState.exact_additional_cost S o.partition H hs f.part
   have len := sources_le_blocks _ _ _ valid
   rw [(OutputState.checked_materialization S o.partition hs f.part).1] at len
   refine ⟨orig,ref,by rw [f.full_cuts] at fullcost len;omega,?_⟩
   intro F hF href
   exact least F (OutputState.original_to_state T S o.partition F ht hs same f.part hF href)

theorem fixed_output_complete (actual : Ordinary) (q : Nat) (below : BelowIH q actual)
 (S T : Tree) (A B C D : List Nat) (o : Output)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup) (same : ∀ x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (he : pairwiseEmbeddings S [A,B,C]=true)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false)
 (badC : restrictionAgrees S T C=false) (hac : Disj T A C) (hbc : Disj T B C)
 (ho : o∈BothBad.outputs S A B D q) (F : Forest) (ha : agreement T S F=true)
 (href : RestrictionBridge.Refines F o.partition) (budget : F.length-1≤q) :
 ∃ H,answerFor actual T S A B C q o=some H ∧ H.length≤F.length := by
 obtain ⟨js,prep,bad,proper,part,own,cross,f⟩ := output_jobs S T A B C D q o hs ht same hp he badA badB badC hac hbc ho
 have paid := output_affordable S A B D q o ho
 have binding := runOutput_binding actual T S A B C q o paid js prep
 have belowb : BelowIH (q-o.sourceCuts.length) actual :=
   fun r hr => below r (Nat.lt_of_lt_of_le hr (Nat.sub_le _ _))
 have original := OutputState.original_to_state T S o.partition F ht hs same f.part ha href
 have fullcost := OutputState.exact_additional_cost S o.partition F hs f.part
 have len := sources_le_blocks _ _ _ original
 rw [(OutputState.checked_materialization S o.partition hs f.part).1,f.full_cuts] at len
 have residual : additionalCost (OutputState.sourceForest S o.partition) F≤q-o.sourceCuts.length := by
   rw [fullcost,f.full_cuts];omega
 obtain ⟨xs,result,_⟩ := grouped_complete actual _ belowb (some T) _ [A++B,C] js prep bad part own F original residual
 have hsnd := grouped_sound actual _ belowb (some T) _ [A++B,C] js prep bad proper part own cross xs result
 exact ⟨xs.flatMap Prod.snd,by simp [answerFor,binding,OutputResult.answer?,meterSchedule_value,result],hsnd.2.2.2 F original⟩
end Universal233.BothBadGrouped
