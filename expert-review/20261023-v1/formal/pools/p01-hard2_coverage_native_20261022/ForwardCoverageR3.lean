import LeafIsolateR3
open RMAF ForestState OutputState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentGeometry IndependentOneExchange ContactedClade ContactedRepair ContactedSource
namespace ContactedForward

theorem split_two_singletons_refines {T S U : Tree} (s : Rule4.Choice T S)
 (sub : CoreGraph.subtree S s.raw.xHead=some U) {F : List (List Nat)}
 (hF : agreement T S F=true) (cF : [s.raw.c]∈F) :
 VertexGeometry.Refines (splitForest (leaves U) F) (Rule4.literalPartition S [s.raw.cHead,s.raw.xHead]) := by
 have proper := choice_proper s
 have ready := original_clade_split_full proper sub hF
 have cG := split_keeps_singleton (leaves U) F cF
 have checks := ready.1
 simp only [agreement,Bool.and_eq_true] at checks
 have labels := partition_labels checks.1.1.1.2
 have shape := (choice_admission_own s).2.2.2.2
 simp only [Rule4.literalPartition,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
  List.all_cons,List.all_nil,Bool.and_true,shape,subtree_labels_lookup sub]
 intro B hb
 obtain ⟨D,hd,bd⟩ := ready.2.2 B hb
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
 rcases hd with rfl|rfl
 · exact ⟨leaves U,List.mem_cons_of_mem _ List.mem_cons_self,bd⟩
 · by_cases yes : s.raw.c∈B
   · have eq := singleton_block_eq proper ready.1 cG hb yes
     exact ⟨[s.raw.c],List.mem_cons_self,fun x hx=>eq ▸ hx⟩
   · refine ⟨(leaves S).filter (fun x=>![s.raw.c].contains x && !(leaves U).contains x),
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),?_⟩
     intro x hx
     refine List.mem_filter.2 ⟨labels B hb x hx,?_⟩
     have nc : x≠s.raw.c := fun eq=>yes (eq ▸ hx)
     have nx := (List.mem_filter.1 (bd x hx)).2
     simp only [Bool.and_eq_true]
     exact ⟨by simpa only [Bool.not_eq_true',←Bool.not_eq_true,List.contains_iff_mem,List.mem_singleton] using nc,nx⟩

theorem two_singletons_exchange {T S : Tree} (s : Rule4.Choice T S) {F : List (List Nat)}
 (hF : agreement T S F=true) (bF : [s.raw.b]∈F) (cF : [s.raw.c]∈F) :
 ∃H,agreement T S H=true ∧ H.length≤F.length ∧
 VertexGeometry.Refines H (Rule4.literalPartition S [s.raw.cHead,s.raw.xHead]) := by
 have proper := choice_proper s
 have perm : (cuts S s.raw.a s.raw.b).Perm [s.raw.cHead,s.raw.xHead] := (choice_admission_own s).2.2.2.1
 have cut : s.raw.xHead∈cuts S s.raw.a s.raw.b := perm.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self)
 obtain ⟨U,sub⟩ := vertex_has_subtree S _ (List.mem_filter.1 cut).1
 have ready := original_clade_split_full proper sub hF
 have refActual := split_two_singletons_refines s sub hF cF
 have refOriginal := refines_partition_perm (literal_partition_perm_own S perm.symm) refActual
 rw [literal_pendant_eq] at refOriginal
 have bG := split_keeps_singleton (leaves U) F bF
 have merged := merge_full_all proper (ordered_sound_own T _ _ (choice_admission_own s).1) (fresh_label T) ready.1 refOriginal bG
 refine ⟨mergeCommon s.raw.a s.raw.b (freshLabel T) (splitForest (leaves U) F),merged.1,?_,?_⟩
 · have count := merged.2.1;have splitcount := ready.2.1;omega
 · have refCuts := merged.2.2
   rw [←literal_pendant_eq] at refCuts
   exact refines_partition_perm (literal_partition_perm_own S perm) refCuts

def OriginalCovered (T S : Tree) (b : Rule4.Branch) (H : List (List Nat)) : Prop :=
 agreement T S H=true ∧ VertexGeometry.Refines H b.partition

theorem actual_forward_coverage {T S : Tree} (s : Rule4.Choice T S) :
 ∀F,agreement T S F=true→∃b∈Rule4.branches s,∃H,OriginalCovered T S b H ∧ H.length≤F.length := by
 intro F hF
 have proper := choice_proper s
 have ab := ordered_sound_own T _ _ (choice_admission_own s).1
 have ac := ordered_sound_own S _ _ (choice_admission_own s).2.1
 rcases endpoint_cases_all proper ab hF with aF|bF|both
 · refine ⟨⟨T,S,[Rule4.aHead s],false⟩,List.mem_cons_of_mem _ List.mem_cons_self,F,⟨hF,?_⟩,Nat.le_refl _⟩
   exact isolated_refines s hF aF
 · rcases endpoint_cases_all (proper_swap_own proper) ac (agreement_swap hF) with aF|cF|together
   · refine ⟨⟨T,S,[Rule4.aHead s],false⟩,List.mem_cons_of_mem _ List.mem_cons_self,F,⟨hF,?_⟩,Nat.le_refl _⟩
     exact isolated_refines s hF aF
   · obtain ⟨H,hH,len,ref⟩ := two_singletons_exchange s hF bF cF
     exact ⟨⟨T,S,[s.raw.cHead,s.raw.xHead],false⟩,List.mem_cons_self,H,⟨hH,ref⟩,len⟩
   · refine ⟨⟨S,T,pendantOriginal T s.raw.a s.raw.c,true⟩,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),F,⟨hF,?_⟩,Nat.le_refl _⟩
     exact cohabit_refines_all (proper_swap_own proper) ac (agreement_swap hF) together
 · refine ⟨⟨T,S,[s.raw.cHead,s.raw.xHead],false⟩,List.mem_cons_self,F,⟨hF,?_⟩,Nat.le_refl _⟩
   exact refines_partition_perm (literal_partition_perm_own S (choice_admission_own s).2.2.2.1)
    (cohabit_refines_all proper ab hF both)

end ContactedForward

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedForward.split_two_singletons_refines
#print axioms ContactedForward.split_two_singletons_refines
#check @ContactedForward.two_singletons_exchange
#print axioms ContactedForward.two_singletons_exchange
#check @ContactedForward.actual_forward_coverage
#print axioms ContactedForward.actual_forward_coverage
