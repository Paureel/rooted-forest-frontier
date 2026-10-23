import OutputRun
namespace Universal233.BothBadGrouped
open RMAF CoreProgram SourceCoverage PairAssembly BinaryCheap RankConsumer
open ForestState ForestGroups RestrictionBridge PaidQueries GroupedFullQuery
open VertexGeometry BinaryExchange

theorem mass_shift (c : Rat) (hc : 2≤c) (q b paid : Nat) (calls : List Nat)
 (eq : b+paid=q) (caps : ∀ r∈calls,r≤b) :
 actualQueryMass c q calls=c^(-(paid:Int))*actualQueryMass c b calls := by
 have cn : c≠0 := Rat.ne_of_gt (by grind : 0<c)
 induction calls with
 | nil => simp [actualQueryMass]
 | cons r rs ih =>
   have cap := caps r (by simp)
   have tail := ih (fun k hk => caps k (by simp [hk]))
   have exp : -((q-r:Nat):Int)=-(paid:Int)+-((b-r:Nat):Int) := by omega
   simp only [actualQueryMass,List.map_cons,List.sum_cons] at tail ⊢
   rw [exp,Rat.zpow_add cn,tail,Rat.mul_add]

theorem output_trace_mass (actual : Ordinary) (q : Nat) (S T : Tree) (A B C D : List Nat) (o : Output)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup) (same : ∀ x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (he : pairwiseEmbeddings S [A,B,C]=true)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false)
 (badC : restrictionAgrees S T C=false) (hac : Disj T A C) (hbc : Disj T B C)
 (ho : o∈BothBad.outputs S A B D q) (c : Rat) (hc : 2≤c) :
 actualQueryMass c q ((traceFor actual T S A B C q o).map Prod.snd)≤
 c^(-(o.sourceCuts.length:Int))*c^(-1:Int) := by
 obtain ⟨js,prep,bad,_,_,_,_,_⟩ := output_jobs S T A B C D q o hs ht same hp he badA badB badC hac hbc ho
 have paid := output_affordable S A B D q o ho
 have binding := runOutput_binding actual T S A B C q o paid js prep
 have trace : traceFor actual T S A B C q o=fullTrace actual (q-o.sourceCuts.length) js := by
   simp [traceFor,binding,OutputResult.trace,fullTrace]
 rw [trace]
 have caps : ∀ r∈(fullTrace actual (q-o.sourceCuts.length) js).map Prod.snd,r≤q-o.sourceCuts.length := by
   intro r hr
   obtain ⟨pb,hpb,eq⟩ := List.mem_map.1 hr
   rw [←eq]
   exact Nat.le_of_lt (fullTrace_strict actual _ js bad pb.1 pb.2 hpb)
 rw [mass_shift c hc q (q-o.sourceCuts.length) o.sourceCuts.length _ (by omega) caps]
 exact Rat.mul_le_mul_of_nonneg_left (fullTrace_mass actual _ js bad c hc)
   (Rat.le_of_lt (Rat.zpow_pos (by grind : 0<c)))

theorem selected_output_cuts (S T : Tree) (A B C : List Nat) (edge : RMAF.Vertex × RMAF.Vertex)
 (q : Nat) (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀ x,x∈leaves T ↔ x∈leaves S) (hp : partitionCheck (leaves S) [A,B,C]=true)
 (selected : PairGeometry.choose T A B=some (.edge edge)) (o : Output)
 (ho : o∈BothBad.outputs S A B (PairGeometry.descendants T edge.2) q) : 3≤o.sourceCuts.length := by
 have ranks := BothBad.selected_ranks S T A B C edge ht (fun x hx => (same x).2 hx) hp selected
 rcases List.mem_append.1 ho with ho|ho
 · have low := generate_color_cost S _ q o ho
   change RankDichotomy.inputRank S (cheapColor A B (PairGeometry.descendants T edge.2))≤o.sourceCuts.length+1 at low
   rw [ranks.1] at low
   omega
 · have low := generate_color_cost S _ q o ho
   change RankDichotomy.inputRank S (cheapColor B A (PairGeometry.descendants T edge.2))≤o.sourceCuts.length+1 at low
   rw [ranks.2] at low
   omega

theorem cheap_output_mass (actual : Ordinary) (q : Nat) (S T : Tree) (A B C D : List Nat) (o : Output)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup) (same : ∀ x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (he : pairwiseEmbeddings S [A,B,C]=true)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false)
 (badC : restrictionAgrees S T C=false) (hac : Disj T A C) (hbc : Disj T B C)
 (ho : o∈BothBad.outputs S A B D q) (cheap : o.sourceCuts.length=3) (c : Rat) (hc : 2≤c) :
 actualQueryMass c q ((traceFor actual T S A B C q o).map Prod.snd)≤c^(-4:Int) := by
 have h := output_trace_mass actual q S T A B C D o hs ht same hp he badA badB badC hac hbc ho c hc
 rw [cheap] at h
 have eq : c^(-((3:Nat):Int))*c^(-1:Int)=c^(-4:Int) := by
   rw [←Rat.zpow_add (Rat.ne_of_gt (by grind : 0<c))];rfl
 simpa only [eq] using h

def allTrace (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat) (xs : List Output) : List (Problem × Nat) :=
 xs.flatMap (traceFor actual T S A B C q)

theorem mass_append (c : Rat) (q : Nat) (xs ys : List Nat) :
 actualQueryMass c q (xs++ys)=actualQueryMass c q xs+actualQueryMass c q ys := by
 simp [actualQueryMass,List.map_append,List.sum_append]

theorem outputs_mass_bound (actual : Ordinary) (q : Nat) (T S : Tree) (A B C : List Nat)
 (xs : List Output) (c : Rat) (hc : 2≤c)
 (bound : ∀ o∈xs,actualQueryMass c q ((traceFor actual T S A B C q o).map Prod.snd)≤
   c^(-(o.sourceCuts.length:Int))*c^(-1:Int)) :
 actualQueryMass c q ((allTrace actual T S A B C q xs).map Prod.snd)≤rawQMass c xs*c^(-1:Int) := by
 induction xs with
 | nil => simp [allTrace,actualQueryMass,rawQMass]
 | cons o xs ih =>
   have hb := bound o (by simp)
   have ht := ih (fun p hp => bound p (by simp [hp]))
   simp only [allTrace,List.flatMap_cons,List.map_append,mass_append] at ht ⊢
   change _≤(c^(-(o.sourceCuts.length:Int))+rawQMass c xs)*c^(-1:Int)
   rw [Rat.add_mul]
   exact qadd_le_add hb ht

theorem actual_pair_mass (actual : Ordinary) (q : Nat) (S T : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex × RMAF.Vertex) (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀ x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (he : pairwiseEmbeddings S [A,B,C]=true)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false)
 (badC : restrictionAgrees S T C=false) (hac : Disj T A C) (hbc : Disj T B C)
 (selected : PairGeometry.choose T A B=some (.edge edge)) (c : Rat) (hc : 2≤c) :
 actualQueryMass c q ((allTrace actual T S A B C q (BothBad.outputs S A B (PairGeometry.descendants T edge.2) q)).map Prod.snd)≤
 2*c^(-4:Int) := by
 have main := outputs_mass_bound actual q T S A B C (BothBad.outputs S A B (PairGeometry.descendants T edge.2) q) c hc
   (fun o ho => output_trace_mass actual q S T A B C _ o hs ht same hp he badA badB badC hac hbc ho c hc)
 have ranks := BothBad.selected_ranks S T A B C edge ht (fun x hx => (same x).2 hx) hp selected
 have raw1 := generate_rawQ_mass S (cheapColor A B (PairGeometry.descendants T edge.2)) q c hc
 have raw2 := generate_rawQ_mass S (cheapColor B A (PairGeometry.descendants T edge.2)) q c hc
 change rawQMass c (generate S (cheapColor A B (PairGeometry.descendants T edge.2)) q).outputs≤c^(1-(RankDichotomy.inputRank S (cheapColor A B (PairGeometry.descendants T edge.2)):Int)) at raw1
 rw [ranks.1] at raw1
 change rawQMass c (generate S (cheapColor B A (PairGeometry.descendants T edge.2)) q).outputs≤c^(1-(RankDichotomy.inputRank S (cheapColor B A (PairGeometry.descendants T edge.2)):Int)) at raw2
 rw [ranks.2] at raw2
 have raw : rawQMass c (BothBad.outputs S A B (PairGeometry.descendants T edge.2) q)≤2*c^(-3:Int) := by
   change rawQMass c ((generate S (cheapColor A B (PairGeometry.descendants T edge.2)) q).outputs++
     (generate S (cheapColor B A (PairGeometry.descendants T edge.2)) q).outputs)≤_
   simp only [rawQMass,List.map_append,List.sum_append] at raw1 raw2 ⊢
   grind
 have mul := Rat.mul_le_mul_of_nonneg_right raw (Rat.le_of_lt (Rat.zpow_pos (by grind : 0<c)))
 have eq : (2*c^(-3:Int))*c^(-1:Int)=2*c^(-4:Int) := by
   rw [Rat.mul_assoc,←Rat.zpow_add (Rat.ne_of_gt (by grind : 0<c))];rfl
 exact Rat.le_trans main (by simpa only [eq] using mul)
end Universal233.BothBadGrouped
