import BinaryCallerPayload
namespace GenericForest.BinaryCaller
open GenericForest.BinaryProvider GenericForest.ScalarBits GenericForest.CheckCorrespondence
open Universal233.WholeSourceWork

/-- This is precisely the singleton check continuation in ForestProgram.solve.
The callee representation equation is explicit; no Nat-to-bit adapter runs. -/
theorem singleton_actual_call
 (ordinary : RMAF.Tree→RMAF.Tree→Nat→Option (List (List Nat)))
 (t s : BinaryProvider.Tree) (q : Bits) (candidate : Option BinaryProvider.Forest)
 (represented : forestOptionValue candidate=ordinary (treeValue t) (treeValue s) (labelValue q)) :
 forestOptionValue (checkOptional (some t) [s] q candidate).value=
  (ordinary (treeValue t) (treeValue s) (labelValue q)).bind
   (GenericForest.checked (some (treeValue t)) [treeValue s] (labelValue q)) := by
 rw [singleton_site,represented]

/-- Exact disjointSolve continuation after its scheduler answers. -/
theorem disjoint_actual_call {α : Type}
 (ordinary : RMAF.Tree→RMAF.Tree→Nat→Option (List (List Nat)))
 (t : BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (q : Bits)
 (answers : Option (List (α×BinaryProvider.Forest)))
 (represented : answers.map (fun xs=>forestValue (xs.flatMap Prod.snd))=
  (GenericForest.disjointAttempt (treeValue t) (sourcesValue ss) ordinary (labelValue q)).bind
   (fun r=>r.answers.map (fun xs=>xs.flatMap Prod.snd))) :
 forestOptionValue (disjointFinish t ss q answers).value=
  GenericForest.disjointSolve (treeValue t) (sourcesValue ss) ordinary (labelValue q) := by
 rw [disjoint_site,represented]
 unfold GenericForest.disjointSolve
 cases h : GenericForest.disjointAttempt (treeValue t) (sourcesValue ss) ordinary (labelValue q) with
 | none=>rfl
 | some r=>cases k : r.answers <;> simp only [Option.bind,k,Option.map_none,Option.map_some]

/-- Literal filterMap expression from the raw-parent branch of ForestProgram.solve. -/
theorem raw_parent_actual_call
 (ordinary : RMAF.Tree→RMAF.Tree→Nat→Option (List (List Nat)))
 (t : BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (q : Bits) (h : GenericForest.Overlap)
 (candidates : List BinaryProvider.Forest)
 (represented : candidates.map forestValue=
  (GenericForest.branches (treeValue t) (sourcesValue ss) h (labelValue q)).filterMap (fun io=>
   let d:=io.2.sourceCuts.length
   if 1≤d ∧ d≤labelValue q then
    GenericForest.solve ordinary (some (treeValue t)) (GenericForest.replace (sourcesValue ss) io.1 io.2.partition) (labelValue q-d)
   else none)) :
 forestOptionValue (bestCandidates (some t) ss q candidates).value=
  RMAF.best List.length (GenericForest.accepted (some (treeValue t)) (sourcesValue ss) (labelValue q))
   ((GenericForest.branches (treeValue t) (sourcesValue ss) h (labelValue q)).filterMap (fun io=>
    let d:=io.2.sourceCuts.length
    if 1≤d ∧ d≤labelValue q then
     GenericForest.solve ordinary (some (treeValue t)) (GenericForest.replace (sourcesValue ss) io.1 io.2.partition) (labelValue q-d)
    else none)) := by
 have p:=raw_parent_site (some t) ss q candidates
 simpa only [represented,targetValue,Option.map_some] using p

theorem generic_returned_nat_sizes
 (ordinary : RMAF.Tree→RMAF.Tree→Nat→Option (List (List Nat)))
 (T : Option RMAF.Tree) (ss : List RMAF.Tree) (q : Nat) (F : List (List Nat)) (N : Nat)
 (tn : targetNodes T≤N) (answer : GenericForest.solve ordinary T ss q=some F) :
 F.length≤N ∧ F.flatten.length≤N := by
 have a:=ForestState.agrees_parts _ _ _ (GenericForest.solve_sound ordinary _ _ _ _ answer).1
 have nd:=(ForestState.proper_parts _ _ a.1).1
 have blocks:=Universal233.SourceCoverage.partitionCheck_block_bound _ _ a.2.1
 have cells:=(RestrictionBridge.checked_flatten_perm _ _ nd a.2.1).length_eq
 have labels:=labels_nodes T
 constructor <;> omega

theorem raw_parent_candidate_sizes
 (ordinary : RMAF.Tree→RMAF.Tree→Nat→Option (List (List Nat)))
 (t : BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (q : Bits) (h : GenericForest.Overlap)
 (N : Nat) (tn : targetNodes (some (treeValue t))≤N)
 (F : List (List Nat))
 (member : F∈(GenericForest.branches (treeValue t) (sourcesValue ss) h (labelValue q)).filterMap (fun io=>
   let d:=io.2.sourceCuts.length
   if 1≤d ∧ d≤labelValue q then
    GenericForest.solve ordinary (some (treeValue t)) (GenericForest.replace (sourcesValue ss) io.1 io.2.partition) (labelValue q-d)
   else none)) : F.length≤N ∧ F.flatten.length≤N := by
 obtain ⟨io,hio,e⟩:=List.mem_filterMap.mp member
 dsimp only at e
 split at e
 · exact generic_returned_nat_sizes ordinary _ _ _ F N tn e
 · contradiction
end GenericForest.BinaryCaller
