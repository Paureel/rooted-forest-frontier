import PaidOutputDefs
namespace Universal233.Hard2PaidLocal
open RMAF CoreProgram SourceCoverage VertexGeometry BothBad BothBadLocal PaidAssembly

theorem runOutputs_sound (actual : Ordinary) (T S : Tree) (q : Nat) (outs : List Output) (H : Forest)
 (answer : (runOutputs actual T S q outs).answer=some H) : agreement T S H=true ∧ H.length-1≤q :=
 execute_sound (GenericForest.solve actual) T S q _ H answer

/-- Every retained occurrence makes its literal whole-source-forest call. -/
theorem runOutputs_call_payment (actual : Ordinary) (T S : Tree) (q : Nat) (outs : List Output) (call : Call)
 (mem : call∈(runOutputs actual T S q outs).calls) :
 ∃o,o∈outs ∧ call.target=some T ∧ call.sources=OutputState.sourceForest S o.partition ∧
 call.budget+o.sourceCuts.length=q := by
 change call∈(execute (GenericForest.solve actual) T S q (entries q .full outs)).calls at mem
 rw [execute_calls] at mem
 obtain ⟨e,he,hcall⟩ := List.mem_flatMap.1 mem
 obtain ⟨ho,mode,afford,payment⟩ := entries_sound q .full outs e he
 cases e with
 | mk o m b =>
  dsimp only at mode payment ho hcall
  subst m
  have eq : call=⟨some T,OutputState.sourceForest S o.partition,b⟩ := by simpa [dispatch] using hcall
  subst call
  exact ⟨o,ho,rfl,rfl,by simpa [Mode.extra] using payment⟩

theorem runOutputs_family_calls_strict (actual : Ordinary) (T S : Tree) (q : Nat) (A B C : List Nat) (kind : Kind)
 (hs : (leaves S).Nodup) (hp : partitionCheck (leaves S) [A,B,C]=true) (call : Call)
 (mem : call∈(runOutputs actual T S q (outputs kind S T A B q)).calls) :
 call.budget+2≤q ∧ call.budget<q := by
 obtain ⟨o,ho,_,_,pay⟩ := runOutputs_call_payment actual T S q _ call mem
 have paid := (generated_output_facts kind hs hp ho).2.2.2.2.1
 exact ⟨by omega,by omega⟩

/-- Counts every retained duplicate occurrence and every failing forest call. -/
theorem runOutputs_trace_mass (actual : Ordinary) (T S : Tree) (q : Nat) (outs : List Output)
 (c : Rat) (base : 2≤c) : traceMass c q (runOutputs actual T S q outs).calls≤rawQMass c outs := by
 change traceMass c q (execute (GenericForest.solve actual) T S q (entries q .full outs)).calls≤_
 rw [execute_mass]
 exact full_entries_mass (GenericForest.solve actual) T S c base q outs

theorem runOutputs_cover (actual : Ordinary) (T S : Tree) (q : Nat) (A B C : List Nat) (kind : Kind)
 (P : Forest) (F : Forest) (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀x,x∈leaves S ↔ x∈leaves T)
 (hp : partitionCheck (leaves S) [A,B,C]=true)
 (hF : agreement T S F=true) (budget : F.length-1≤q) (IH : BelowIH q actual)
 (cover : ∃o,o∈outputs kind S T A B q ∧ OutputWitness S P F q o) :
 ∃H,(runOutputs actual T S q (outputs kind S T A B q)).answer=some H ∧
 agreement T S H=true ∧ H.length-1≤q ∧ H.length≤F.length := by
 obtain ⟨o,mem,witness⟩ := cover
 obtain ⟨ca,cb,cc,generated⟩ := outputs_generated kind S T A B q o mem
 obtain ⟨part,embed,real,shape,paid,afford⟩ := generated_output_facts kind hs hp mem
 let b:=q-o.sourceCuts.length
 have low : b<q := by dsimp [b]; omega
 have refQ : RestrictionBridge.Refines F o.partition := by
  intro K hK
  obtain ⟨U,hU,sub⟩ := witness.1 K hK
  exact ⟨U,hU,fun x hx=>sub x hx⟩
 have remaining := generated_residual_budget T S (WholeSourceMass.taggedColor A B ca cb cc) o q q F hs ht
  (fun x=>(same x).symm) generated hF refQ budget
 have exactness := forest_exact_at_local actual b (IH b low) (some T) (OutputState.sourceForest S o.partition) b (Nat.le_refl _)
 obtain ⟨H,answer,agree,refine,bound,len⟩ := full_candidate (GenericForest.solve actual) T S
  (WholeSourceMass.taggedColor A B ca cb cc) o q b F hs ht (fun x=>(same x).symm) generated hF refQ
  (by dsimp [b]; omega) exactness
 have entry : (⟨o,.full,b⟩ : Entry)∈entries q .full (outputs kind S T A B q) := by
  simpa only [b,Mode.extra,Nat.sub_zero] using entries_complete q .full _ o mem (by simpa [Mode.extra] using afford)
 obtain ⟨G,hG,glen⟩ := execute_complete (GenericForest.solve actual) T S q _ _ entry H answer agree
  (Nat.le_trans (Nat.sub_le_sub_right len 1) budget)
 have sound := execute_sound (GenericForest.solve actual) T S q _ G hG
 exact ⟨G,hG,sound.1,sound.2,Nat.le_trans glen len⟩

theorem runOutputs_minimum_covered (actual : Ordinary) (T S : Tree) (q : Nat) (A B C : List Nat) (kind : Kind)
 (P : Forest) (H : Forest) (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀x,x∈leaves S ↔ x∈leaves T) (hp : partitionCheck (leaves S) [A,B,C]=true)
 (IH : BelowIH q actual) (answer : (runOutputs actual T S q (outputs kind S T A B q)).answer=some H) :
 agreement T S H=true ∧ H.length-1≤q ∧
 ∀F,agreement T S F=true → F.length-1≤q →
 (∃o,o∈outputs kind S T A B q ∧ OutputWitness S P F q o) → H.length≤F.length := by
 obtain ⟨agree,budget⟩ := runOutputs_sound actual T S q _ H answer
 refine ⟨agree,budget,?_⟩
 intro F hF cost cover
 obtain ⟨G,hG,_,_,len⟩ := runOutputs_cover actual T S q A B C kind P F hs ht same hp hF cost IH cover
 have eq : G=H := Option.some.inj (hG.symm.trans answer)
 simpa [eq] using len
end Universal233.Hard2PaidLocal
