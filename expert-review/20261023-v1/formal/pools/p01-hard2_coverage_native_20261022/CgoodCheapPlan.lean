import OrdinaryEntryInterface
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge OutputState Universal233 Universal233.CoreProgram
namespace ContactedHard2Survival

theorem entries_member (q : Nat) (mode : BothBad.Mode) (outs : List Output) (o : Output)
 (member : o∈outs) (paid : o.sourceCuts.length+mode.extra≤q) :
 (⟨o,mode,q-o.sourceCuts.length-mode.extra⟩ : BothBad.Entry)∈BothBad.entries q mode outs := by
 apply List.mem_filterMap.mpr
 exact ⟨o,member,by rw [ite_eq_left paid]⟩

theorem execution_entry_cover (solve : BothBad.ForestSolver) (T S : Tree) (q : Nat)
 (es : List BothBad.Entry) (e : BothBad.Entry) (member : e∈es) (H F : List (List Nat))
 (checked : BothBad.checked T S q (BothBad.dispatch solve T S e).answer=some H) (least : H.length≤F.length) :
 ∃G,(BothBad.execute solve T S q es).answer=some G ∧ agreement T S G=true ∧ G.length≤F.length := by
 obtain ⟨G,runG,le⟩:=execute_member_no_larger solve T S q es e member H checked
 exact ⟨G,runG,(execute_some_sound solve T S q es G runG).1,Nat.le_trans le least⟩

theorem opposite_reuse_payment (T S : Tree) (A B C D : List Nat) (q : Nat)
 (proper : DepthOne.proper T S=true) (parents : partitionCheck (leaves S) [A,B,C]=true)
 (o : Output) (member : o∈BothBad.reuse S (edgeCheapColor B A D) (generate S (edgeCheapColor B A D) 3).outputs q)
 (real : CutRealization.RealizedOutput S o) : o.partition.length=o.sourceCuts.length+1 ∧ 2≤o.sourceCuts.length := by
 change o∈(if (generate S (edgeCheapColor B A D) 3).outputs.isEmpty then
  (generate S (edgeCheapColor B A D) q).outputs else (generate S (edgeCheapColor B A D) 3).outputs) at member
 split at member
 · exact (whole_source_payment T S A B C q (fun _=>0) (sideColor D) (fun _=>0) proper parents o member real).2.2
 · exact (whole_source_payment T S A B C 3 (fun _=>0) (sideColor D) (fun _=>0) proper parents o member real).2.2

theorem cheapPlan_coverage (ordinary : PaidInstances.OrdinarySolver) (q : Nat) (T S : Tree)
 (A B C : List Nat) (e : RMAF.Vertex×RMAF.Vertex) (F : List (List Nat))
 (below : PaidInstances.BelowBudget ordinary q)
 (contract : ParentExecutionContract (GenericForest.solve (PaidInstances.OwnPaid ordinary q)) q)
 (proper : DepthOne.proper T S=true) (parents : partitionCheck (leaves S) [A,B,C]=true)
 (swapped : partitionCheck (leaves S) [B,A,C]=true) (sourceEmb : pairwiseEmbeddings S [A,B,C]=true)
 (edge : e∈PairGeometry.edges T) (clearAB : PairGeometry.ActualClear T A B e.2)
 (clearAC : Clear (minimalVertices A T) (minimalVertices C T))
 (clearBC : Clear (minimalVertices B T) (minimalVertices C T))
 (xa ya xb yb : Nat) (xaA : xa∈A) (yaA : ya∈A) (xbB : xb∈B) (ybB : yb∈B)
 (xaD : xa∈PairGeometry.descendants T e.2) (yaN : ya∉PairGeometry.descendants T e.2)
 (xbD : xb∈PairGeometry.descendants T e.2) (ybN : yb∉PairGeometry.descendants T e.2)
 (badA : restrictionAgrees S T A=false) (goodC : restrictionAgrees S T C=true)
 (agree : agreement T S F=true) (ref : VertexGeometry.Refines F [A,B,C]) (budget : F.length-1≤q)
 (cheapNonempty : (generate S (edgeCheapColor A B (PairGeometry.descendants T e.2)) 3).outputs≠[]) :
 ∃G,(BothBad.execute (GenericForest.solve (PaidInstances.OwnPaid ordinary q)) T S q
  (BothBad.cheapPlan S T A B C (PairGeometry.descendants T e.2)
   q (generate S (edgeCheapColor A B (PairGeometry.descendants T e.2)) 3).outputs
   (BothBad.reuse S (edgeCheapColor B A (PairGeometry.descendants T e.2))
    (generate S (edgeCheapColor B A (PairGeometry.descendants T e.2)) 3).outputs q))).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 let D:=PairGeometry.descendants T e.2
 let cheap:=(generate S (edgeCheapColor A B D) 3).outputs
 let opposite:=BothBad.reuse S (edgeCheapColor B A D) (generate S (edgeCheapColor B A D) 3).outputs q
 let solve:=GenericForest.solve (PaidInstances.OwnPaid ordinary q)
 let es:=BothBad.cheapPlan S T A B C D q cheap opposite
 change ∃G,(BothBad.execute solve T S q es).answer=some G ∧ agreement T S G=true ∧ G.length≤F.length
 obtain ⟨probe,probeMember⟩:=List.exists_mem_of_ne_nil cheap cheapNonempty
 have availability : (restrictionAgrees S T (BinaryCheap.ay A D) && restrictionAgrees S T (BinaryCheap.an A D))=true→
   ∃known,BothBad.knownOne T S A=some known := by
  intro good
  have guards : restrictionAgrees S T (BinaryCheap.ay A D)=true ∧ restrictionAgrees S T (BinaryCheap.an A D)=true:=by simpa only [Bool.and_eq_true] using good
  exact cheap_probe_knownOne T S A B C e proper parents swapped edge xa ya xaA yaA xaD yaN probe probeMember
   guards.1 guards.2 badA
 have alternative:=side_parent_alternative T S A B e F proper agree (partition_parent_apart _ _ _ _ parents).1 edge
 rcases alternative with ma|mb
 · have pp:=IndependentReconstruction.proper_parts proper
   have monoF : ∀K,K∈F→LabelMonochromatic (edgeCheapColor A B D) K := by
    have refSwap : VertexGeometry.Refines F [B,A,C]:=by
     intro K kF
     obtain ⟨U,uQ,sub⟩:=ref K kF
     exact ⟨U,(List.Perm.swap B A [C]).mem_iff.mp uQ,sub⟩
    have apart:=partition_parent_apart _ _ _ _ swapped
    exact tagged_monochrome F B A C (fun _=>0) (sideColor D) (fun _=>0) refSwap apart.1 apart.2.1 apart.2.2
     (constant_monochrome F B) ma (constant_monochrome F C)
   have scope:=cheap_probe_saturation S A B C D parents pp.2.1 xa ya xaA yaA xaD yaN probe probeMember
   have refF:=scope.2.2.2.2 F (agreement_source_partition T S F agree) monoF
   have targetEmb:=cheap_probe_target_embedding T S A B C e proper parents swapped edge xa ya xaA yaA xaD yaN
    probe probeMember clearAB clearAC clearBC
   have pay:=whole_source_payment T S B A C 3 (fun _=>0) (sideColor D) (fun _=>0) proper swapped probe probeMember scope.1
   obtain ⟨afford,_,H,runH,_,least⟩:=literal_ordinary_dispatch_complete solve q T S contract proper probe scope.2.1
    scope.2.2.1 targetEmb pay.2.2.1 (by omega) F agree refF budget
   have ent : (⟨probe,.ordinary,q-probe.sourceCuts.length⟩ : BothBad.Entry)∈BothBad.entries q .ordinary cheap:=by
    simpa only [BothBad.Mode.extra,Nat.add_zero,Nat.sub_zero] using entries_member q .ordinary cheap probe probeMember (by simpa only [BothBad.Mode.extra,Nat.add_zero] using afford)
   have esMember : (⟨probe,.ordinary,q-probe.sourceCuts.length⟩ : BothBad.Entry)∈es:=by
    by_cases good : (restrictionAgrees S T (BinaryCheap.ay A D) && restrictionAgrees S T (BinaryCheap.an A D))=true
    · obtain ⟨known,runKnown⟩:=availability good
      change _∈BothBad.cheapPlan S T A B C D q cheap opposite
      delta BothBad.cheapPlan
      rw [ite_eq_left good,runKnown]
      exact List.mem_append.mpr (Or.inl ent)
    · change _∈BothBad.cheapPlan S T A B C D q cheap opposite
      delta BothBad.cheapPlan
      rw [ite_eq_right good]
      exact List.mem_append.mpr (Or.inl ent)
   exact execution_entry_cover solve T S q es _ esMember H F runH least
 · obtain ⟨_,o,member,real,part,emb,refF,refP,_,_,oneA,oneC,refJ,monoB⟩:=
    retained_opposite_output T S A B C D q F proper parents swapped sourceEmb agree ref mb budget xb yb xbB ybB xbD ybN
   have payment:=opposite_reuse_payment T S A B C D q proper parents o member real
   by_cases good : (restrictionAgrees S T (BinaryCheap.ay A D) && restrictionAgrees S T (BinaryCheap.an A D))=true
   · obtain ⟨known,runKnown⟩:=availability good
     obtain ⟨afford,_,H,runH,_,least⟩:=literal_retained_dispatch_complete ordinary q T S A B C e.2 o (retainedSource A B C F)
      known F below proper parents part emb refP payment.1 oneA oneC refJ
      (by dsimp only [retainedSource];exact List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))
      (by dsimp only [retainedSource];exact List.mem_append_right _ List.mem_cons_self) agree refF badA goodC budget runKnown monoB clearAB clearAC clearBC
     have ent:=entries_member q (.retained A B C known) opposite o member (by simpa only [BothBad.Mode.extra] using afford)
     have esMember : (⟨o,.retained A B C known,q-o.sourceCuts.length-1⟩ : BothBad.Entry)∈es:=by
      change _∈BothBad.cheapPlan S T A B C D q cheap opposite
      delta BothBad.cheapPlan
      rw [ite_eq_left good,runKnown]
      exact List.mem_append.mpr (Or.inr ent)
     exact execution_entry_cover solve T S q es _ esMember H F runH least
   · obtain ⟨afford,_,H,runH,_,least⟩:=literal_full_dispatch_complete ordinary q T S below proper o part emb payment.1
      (by omega) F agree refF budget
     have ent:=entries_member q .full opposite o member (by simpa only [BothBad.Mode.extra,Nat.add_zero] using afford)
     have esMember : (⟨o,.full,q-o.sourceCuts.length⟩ : BothBad.Entry)∈es:=by
      change _∈BothBad.cheapPlan S T A B C D q cheap opposite
      delta BothBad.cheapPlan
      rw [ite_eq_right good]
      exact List.mem_append.mpr (Or.inr (by simpa only [BothBad.Mode.extra,Nat.sub_zero] using ent))
     exact execution_entry_cover solve T S q es _ esMember H F runH least
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.entries_member
#print axioms ContactedHard2Survival.entries_member
#check @ContactedHard2Survival.execution_entry_cover
#print axioms ContactedHard2Survival.execution_entry_cover
#check @ContactedHard2Survival.opposite_reuse_payment
#print axioms ContactedHard2Survival.opposite_reuse_payment
#check @ContactedHard2Survival.cheapPlan_coverage
#print axioms ContactedHard2Survival.cheapPlan_coverage
