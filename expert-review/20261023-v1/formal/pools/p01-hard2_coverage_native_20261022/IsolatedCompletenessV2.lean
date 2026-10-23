-- Explicit licensed generic geometry reuse, only at the three isolated consumers.
import PairOptimalV3
open RMAF ForestState ForestGroups RestrictionBridge Universal233
namespace ContactedHard2Overlap

theorem proper_input_of_partition (T : Tree) (P : List (List Nat))
 (properT : (leaves T).Nodup) (part : partitionCheck (leaves T) P=true)
 (A B : List Nat) (aP : A∈P) (bP : B∈P) (ne : A≠B) : PairGeometry.properInput T A B=true := by
 have nA:=RestrictionBridge.checked_block_nodup _ _ part A aP
 have nB:=RestrictionBridge.checked_block_nodup _ _ part B bP
 have emptyA : A.isEmpty=false := List.isEmpty_eq_false_iff.mpr (checked_nonempty _ _ part A aP)
 have emptyB : B.isEmpty=false := List.isEmpty_eq_false_iff.mpr (checked_nonempty _ _ part B bP)
 have allA : A.all (fun x=>(leaves T).contains x)=true := by
  apply List.all_eq_true.mpr
  intro x hx
  exact List.contains_iff_mem.mpr (checked_label _ _ part aP hx)
 have allB : B.all (fun x=>(leaves T).contains x)=true := by
  apply List.all_eq_true.mpr
  intro x hx
  exact List.contains_iff_mem.mpr (checked_label _ _ part bP hx)
 have apart : A.all (fun x=>!(B.contains x))=true := by
  apply List.all_eq_true.mpr
  intro x hx
  have no : x∉B := fun hb=>ne (ForestGroups.group_unique _ _ part A B aP bP x hx hb)
  have notContains : B.contains x=false := by
   cases hxB : B.contains x with
   | false => rfl
   | true => exact False.elim (no (List.contains_iff_mem.mp hxB))
  simp only [notContains,Bool.not_false]
 simp only [PairGeometry.properInput,Bool.and_eq_true,decide_eq_true_eq]
 exact ⟨⟨⟨⟨⟨⟨⟨properT,nA⟩,nB⟩,by simp only [emptyA,Bool.not_false]⟩,
  by simp only [emptyB,Bool.not_false]⟩,allA⟩,allB⟩,apart⟩

theorem repeated_common_some (xs ys : List RMAF.Vertex) (v : RMAF.Vertex)
 (h : VertexGeometry.findCommon xs ys ys=some v) : v∈xs ∧ v∈ys := by
 induction xs with
 | nil => simp only [VertexGeometry.findCommon] at h;cases h
 | cons a tail ih =>
  simp only [VertexGeometry.findCommon,Bool.and_self] at h
  cases hc : ys.contains a with
  | false =>
   simp only [hc,Bool.false_eq_true,ite_false] at h
   have found:=ih h
   exact ⟨List.mem_cons_of_mem _ found.1,found.2⟩
  | true =>
   simp only [hc,ite_true,Option.some.injEq] at h
   subst v
   exact ⟨List.mem_cons_self,List.contains_iff_mem.mp hc⟩

theorem source_parent_inputs (T S : Tree) (A B C : List Nat)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true) :
 PairGeometry.properInput T A B=true ∧ PairGeometry.properInput T A C=true ∧ PairGeometry.properInput T B C=true := by
 have pp:=IndependentReconstruction.proper_parts proper
 have targetPart:= (partition_labels_congr (leaves S) (leaves T) [A,B,C] (fun x=>pp.2.2.mem_iff.symm)).1 part
 have nd:=checked_family_nodup _ _ targetPart
 have ab : A≠B := by
  intro eq
  exact (List.nodup_cons.mp nd).1 (by rw [eq];exact List.mem_cons_self)
 have ac : A≠C := by
  intro eq
  exact (List.nodup_cons.mp nd).1 (by rw [eq];exact List.mem_cons_of_mem _ List.mem_cons_self)
 have bc : B≠C := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
 refine ⟨proper_input_of_partition T _ pp.1 targetPart A B List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) ab,
  proper_input_of_partition T _ pp.1 targetPart A C List.mem_cons_self (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) ac,
  proper_input_of_partition T _ pp.1 targetPart B C (List.mem_cons_of_mem _ List.mem_cons_self) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) bc⟩

theorem isolated_abc_complete (T S : Tree) (A B C : List Nat) (v : RMAF.Vertex)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (hab : overlap T A B=some v) (hbc : overlap T B C=none) (hac : overlap T A C=none) :
 ∃choice,select T A B C=some (.pair .abc choice) ∧ PairGeometry.ValidChoice T A B choice := by
 have hp:=(source_parent_inputs T S A B C proper part).1
 have witness:=repeated_common_some _ _ v hab
 obtain ⟨choice,pick,valid⟩:=PairGeometry.choose_complete T A B hp ⟨v,witness⟩
 exact ⟨choice,by simp only [select,hab,hbc,hac,isolated,first,second,pick,Option.map_some],valid⟩

theorem isolated_acb_complete (T S : Tree) (A B C : List Nat) (v : RMAF.Vertex)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (hab : overlap T A B=none) (hbc : overlap T B C=none) (hac : overlap T A C=some v) :
 ∃choice,select T A B C=some (.pair .acb choice) ∧ PairGeometry.ValidChoice T A C choice := by
 have hp:=(source_parent_inputs T S A B C proper part).2.1
 have witness:=repeated_common_some _ _ v hac
 obtain ⟨choice,pick,valid⟩:=PairGeometry.choose_complete T A C hp ⟨v,witness⟩
 exact ⟨choice,by simp only [select,hab,hbc,hac,isolated,first,second,pick,Option.map_some],valid⟩

theorem isolated_bca_complete (T S : Tree) (A B C : List Nat) (v : RMAF.Vertex)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (hab : overlap T A B=none) (hbc : overlap T B C=some v) (hac : overlap T A C=none) :
 ∃choice,select T A B C=some (.pair .bca choice) ∧ PairGeometry.ValidChoice T B C choice := by
 have hp:=(source_parent_inputs T S A B C proper part).2.2
 have witness:=repeated_common_some _ _ v hbc
 obtain ⟨choice,pick,valid⟩:=PairGeometry.choose_complete T B C hp ⟨v,witness⟩
 exact ⟨choice,by simp only [select,hab,hbc,hac,isolated,first,second,pick,Option.map_some],valid⟩
end ContactedHard2Overlap

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Overlap.proper_input_of_partition
#print axioms ContactedHard2Overlap.proper_input_of_partition
#check @ContactedHard2Overlap.repeated_common_some
#print axioms ContactedHard2Overlap.repeated_common_some
#check @ContactedHard2Overlap.source_parent_inputs
#print axioms ContactedHard2Overlap.source_parent_inputs
#check @ContactedHard2Overlap.isolated_abc_complete
#print axioms ContactedHard2Overlap.isolated_abc_complete
#check @ContactedHard2Overlap.isolated_acb_complete
#print axioms ContactedHard2Overlap.isolated_acb_complete
#check @ContactedHard2Overlap.isolated_bca_complete
#print axioms ContactedHard2Overlap.isolated_bca_complete
