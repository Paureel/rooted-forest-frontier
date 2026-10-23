import DisjointRawTraceV3

namespace SourceBothBadRawV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open OrdinaryDispatch.Hard2SourceWork SourceChildMetadataV3 SourceHard2ValuesV3
open SourceOrdinaryMafRawV3

theorem retained_value (known : F) (completed : List Nat) (a : Option F) :
    (retainedReconstructionMeter known completed a).value=a.map (fun F=>known++F++[completed]) := by
  cases a <;> rfl

theorem dispatch_value (actual : GenericForest.FrontierWork.Ordinary)
    (T S : Tree) (e : BothBad.Entry) :
    (bothBadDispatchLocalSource actual T S e).value=
      BothBad.dispatch (GenericForest.solve actual) T S e := by
  cases he:e.mode <;>
    simp only [bothBadDispatchLocalSource,BothBad.dispatch,he,local_raw_value,sourceForest_value,
      localTargetMeter_value,ownedMeter_value,retained_value]

theorem execute_value (actual : GenericForest.FrontierWork.Ordinary)
    (T S : Tree) (q : Nat) (es : List BothBad.Entry) :
    (bothBadExecuteLocalSource actual T S q es).value=
      BothBad.execute (GenericForest.solve actual) T S q es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [bothBadExecuteLocalSource,BothBad.execute,dispatch_value,checkedMeter_value,choose_value,ih]

theorem pair_value (actual : GenericForest.FrontierWork.Ordinary)
    (S T : Tree) (A B C : List Nat) (edge : Vertex×Vertex) (q : Nat) :
    (bothBadLocalPairLocalSource actual S T A B C edge q).value=
      BothBadLocal.runPair actual S T A B C edge q := by
  simp only [bothBadLocalPairLocalSource,pairDescendantsMeter_value,bothBadPlanMeter_value,
    execute_value,BothBadLocal.runPair,BothBad.solvePair]
end SourceBothBadRawV3

namespace SourceBothBadPairV3
open RMAF Universal233 SourceForestV3 SourceCouplingV2
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree} {A B C : List Nat}

theorem pair_raw_execution
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PairExec OrdExec mode T S A B C edge q k r debits slots) :
    r.value=BothBadLocal.runPair (ordinarySpec mode base) S T A B C edge q := by
  rw [pair_source_fields sound h,SourceBothBadRawV3.pair_value]
end SourceBothBadPairV3
