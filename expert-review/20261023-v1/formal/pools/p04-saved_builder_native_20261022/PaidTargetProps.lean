import PaidBottomRows
namespace PaidBuilderAuthor
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local
open Universal233.CoreGraph Universal233.HardParent
open Universal233.Rule5Classification Universal233.Rule5FinalClassification OrdinaryDispatch
open Universal233.Hard2Overlap AdmittedRule5Author
open Universal233.Case322Extraction Universal233.Rule5PaidSelector

theorem literal_second_flags (T : Tree) (X : List Nat) (c : Nat) (u v : Vertex)
 (pick:selectBoundary T X c=some (.second u v)) :
 (incident T X=[u,v] ∨ incident T X=[v,u]) ∧
 paint T X u=false ∧ paint T X v=false ∧
 (outsideCheck T X u c=true ∨ outsideCheck T X v c=false) := by
 cases hi:incident T X with
 | nil => rw [selectBoundary,hi] at pick;cases pick
 | cons q tail =>
  cases tail with
  | nil => rw [selectBoundary,hi] at pick;cases pick
  | cons r rest =>
   cases rest with
   | cons z zs => rw [selectBoundary,hi] at pick;cases pick
   | nil =>
    cases check:outsideCheck T X q c <;> cases pq:paint T X q <;> cases pr:paint T X r
    all_goals simp only [selectBoundary,hi,check,pq,pr,Bool.false_eq_true,ite_false,ite_true] at pick
    all_goals first | cases pick
    · exact ⟨Or.inr rfl,pr,pq,Or.inr check⟩
    · exact ⟨Or.inl rfl,pq,pr,Or.inl check⟩

theorem outside_check_iff (T : Tree) (X : List Nat) (q : Vertex) (c : Nat) :
 outsideCheck T X q c=true ↔ OutsideLabel T X q c := by
 cases hc:(subtreeLabels T q).contains c <;> cases hq:(minimalVertices X T).contains q
 all_goals simp only [outsideCheck,paint,hc,hq,OutsideLabel,←List.contains_iff_mem,hc,hq]
 all_goals decide

theorem outside_label_not_both (T : Tree) (X : List Nat) (q r : Vertex) (z : Nat)
 (hn:(leaves T).Nodup) (hq:q∈incident T X) (hr:r∈incident T X) (neq:q≠r)
 (zT:z∈leaves T) : ¬(OutsideLabel T X q z ∧ OutsideLabel T X r z) := by
 obtain ⟨w,leaf⟩:=CutRealization.leaf_exists zT
 intro both
 exact outside_regions_disjoint hq hr neq
  ⟨(outside_label_at hn leaf).mp both.1,(outside_label_at hn leaf).mp both.2⟩

theorem false_paint_outgoing (T : Tree) (X : List Nat) (q : Vertex)
 (hq:q∈incident T X) (paintFalse:paint T X q=false) : Outgoing T X q := by
 have outside:q∉minimalVertices X T := by
  intro inside
  have hit:=List.contains_iff_mem.mpr inside
  change paint T X q=true at hit
  rw [paintFalse] at hit;cases hit
 rcases boundary_directions hq with incoming|outgoing
 · exact False.elim (outside incoming.1)
 · exact outgoing

theorem outside_label_not_selected (T : Tree) (X : List Nat) (q : Vertex) (z : Nat)
 (hn:(leaves T).Nodup) (hq:q∈incident T X) (zT:z∈leaves T)
 (outside:OutsideLabel T X q z) : z∉X := by
 obtain ⟨w,leaf⟩:=CutRealization.leaf_exists zT
 have notHull:=outside_not_hull hq ((outside_label_at hn leaf).mp outside)
 exact fun selected=>notHull ((Integration.minimalVertices_terminal X T w z leaf).mpr selected)

theorem selected_second_out_regions (T : Tree) (X C : List Nat) (c d : Nat) (u v : Vertex)
 (hn:(leaves T).Nodup) (hp:partitionCheck (leaves T) [X,[c],C]=true)
 (he:pairwiseEmbeddings T [X,[c],C]=true) (dC:d∈C)
 (pick:selectBoundary T X c=some (.second u v)) :
 OutRegion T X u [c] ∧ OutRegion T X v C := by
 obtain ⟨order,pu,pv,check⟩:=literal_second_flags T X c u v pick
 have um:u∈incident T X := by
  rcases order with eq|eq <;> rw [eq]
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
 have vm:v∈incident T X := by
  rcases order with eq|eq <;> rw [eq]
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_self
 have nd:(incident T X).Nodup := (vertices_nodup T).filter _
 have neq:u≠v := by
  intro same;subst v
  rcases order with eq|eq <;> rw [eq] at nd <;>
   exact (List.nodup_cons.mp nd).1 List.mem_cons_self
 have cT:c∈leaves T := block_labels hp (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self
 have dT:d∈leaves T := block_labels hp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) dC
 have choicesU:=boundary_meets_one_other hn hp he dC um
 have choicesV:=boundary_meets_one_other hn hp he dC vm
 have uc:OutsideLabel T X u c := by
  rcases check with cu|cv
  · exact (outside_check_iff T X u c).mp cu
  · rcases choicesU with good|ud
    · exact good
    · rcases choicesV with vc|vd
      · have trueCheck:outsideCheck T X v c=true := (outside_check_iff T X v c).mpr vc
        rw [cv] at trueCheck;cases trueCheck
      · exact False.elim (outside_label_not_both T X u v d hn um vm neq dT ⟨ud,vd⟩)
 have nvc:¬OutsideLabel T X v c := fun vc=>outside_label_not_both T X u v c hn um vm neq cT ⟨uc,vc⟩
 have outU:=false_paint_outgoing T X u um pu
 have outV:=false_paint_outgoing T X v vm pv
 have coreV:∀z,z∈C→OutsideLabel T X v z := by
  intro z zC
  exact (boundary_meets_one_other hn hp he zC vm).resolve_left nvc
 have noCoreU:∀z,z∈C→¬OutsideLabel T X u z := by
  intro z zC uz
  have zT:z∈leaves T := block_labels hp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) zC
  exact outside_label_not_both T X u v z hn um vm neq zT ⟨uz,coreV z zC⟩
 constructor
 · refine ⟨outU,?_⟩
   intro z zT
   constructor
   · intro inside
     have uz:OutsideLabel T X u z := ⟨fun _=>outU.1,fun _=>inside⟩
     obtain ⟨B,member,zB⟩:=Integration.partitionCheck_covers _ _ hp z zT
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with eq|eq|eq
     · rw [eq] at zB
       exact False.elim (outside_label_not_selected T X u z hn um zT uz zB)
     · rw [eq] at zB;exact zB
     · rw [eq] at zB;exact False.elim (noCoreU z zB uz)
   · intro singleton
     have eq:z=c:=List.mem_singleton.mp singleton
     subst z
     exact uc.mpr outU.1
 · refine ⟨outV,?_⟩
   intro z zT
   constructor
   · intro inside
     have vz:OutsideLabel T X v z := ⟨fun _=>outV.1,fun _=>inside⟩
     obtain ⟨B,member,zB⟩:=Integration.partitionCheck_covers _ _ hp z zT
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with eq|eq|eq
     · rw [eq] at zB
       exact False.elim (outside_label_not_selected T X v z hn vm zT vz zB)
     · rw [eq] at zB
       have eq:z=c:=List.mem_singleton.mp zB
       subst z;exact False.elim (nvc vz)
     · rw [eq] at zB;exact zB
   · intro zC
     exact (coreV z zC).mpr outV.1

theorem selected_bad_core_complement (T S : Tree) (a b : Nat) (bad : BadSelection) (z : Nat)
 (len:(cuts S a b).length=2) (pick:selectBad T S a b=some bad) (zS:z∈leaves S) :
 z∈coreLabels S a b ↔ z∉subtreeLabels S bad.badArc ∧ z≠bad.c := by
 have facts:=selectBad_sound T S a b bad pick
 have single:=source_labels_of_subtree S bad.singletonArc (.leaf bad.c) facts.2.2.2.2
 change subtreeLabels S bad.singletonArc=[bad.c] at single
 constructor
 · intro core
   have spec:=(mem_core S a b z).mp core
   refine ⟨spec.2 bad.badArc facts.1,?_⟩
   intro eq
   apply spec.2 bad.singletonArc facts.2.1
   rw [single,eq]
   exact List.mem_cons_self
 · intro rest
   apply (mem_core S a b z).mpr
   refine ⟨zS,?_⟩
   intro q qm
   rcases selected_bad_cut_cases T S a b bad len pick q qm with rfl|rfl
   · exact rest.1
   · rw [single]
     exact fun hit=>rest.2 (List.mem_singleton.mp hit)

theorem cherry_address (T : Tree) (a b : Nat) (cherry:HasCherry a b T) :
 ∃q,CherryAt T q a b ∨ CherryAt T q b a := by
 induction T with
 | leaf x => cases cherry
 | node l r il ir =>
  cases cherry with
  | here => exact ⟨[],Or.inl rfl⟩
  | swap => exact ⟨[],Or.inr rfl⟩
  | left h =>
   obtain ⟨q,location⟩:=il h
   rcases location with h|h
   · exact ⟨false::q,Or.inl h⟩
   · exact ⟨false::q,Or.inr h⟩
  | right h =>
   obtain ⟨q,location⟩:=ir h
   rcases location with h|h
   · exact ⟨true::q,Or.inl h⟩
   · exact ⟨true::q,Or.inr h⟩

theorem tree_has_label (T : Tree) : ∃x,x∈leaves T := by
 induction T with
 | leaf x => exact ⟨x,List.mem_cons_self⟩
 | node l r ih _ =>
  obtain ⟨x,member⟩:=ih
  exact ⟨x,List.mem_append.mpr (Or.inl member)⟩

theorem tree_singleton_of_nodup (T : Tree) (c : Nat) (hn:(leaves T).Nodup)
 (only:∀z,z∈leaves T→z=c) : T=.leaf c := by
 cases T with
 | leaf x =>
  have eq:=only x List.mem_cons_self
  rw [eq]
 | node l r =>
  obtain ⟨x,xL⟩:=tree_has_label l
  obtain ⟨y,yR⟩:=tree_has_label r
  have xc:=only x (List.mem_append.mpr (Or.inl xL))
  have yc:=only y (List.mem_append.mpr (Or.inr yR))
  exact False.elim ((List.nodup_append.mp hn).2.2 x xL y yR (xc.trans yc.symm))

theorem singleton_out_region_leaf (T : Tree) (X : List Nat) (c : Nat) (u : Vertex)
 (hn:(leaves T).Nodup) (um:u∈incident T X) (region:OutRegion T X u [c]) : LeafAt T u c := by
 obtain ⟨U,location⟩:=(incident_spec T X u).mp um |>.1
 have labels:=source_labels_of_subtree T u U location
 have hnU:(leaves U).Nodup := by
  rw [←labels];exact (subtreeLabels_sublist T u).nodup hn
 have only:∀z,z∈leaves U→z=c := by
  intro z zU
  have zLabel:z∈subtreeLabels T u := by rw [labels];exact zU
  have zT:z∈leaves T:=(subtreeLabels_sublist T u).subset zLabel
  exact List.mem_singleton.mp ((region.2 z zT).mp zLabel)
 have eq:U=.leaf c:=tree_singleton_of_nodup U c hnU only
 change subtree T u=some (.leaf c)
 rw [location,eq]

theorem actual_second_literal_props (T S : Tree) (c d : Candidate) (bad : BadSelection) (u v : Vertex)
 (proper:DepthOne.proper T S=true) (early:FastOrdinary.early T S=.hard2 c d)
 (graph:runHard2 T S c=some .disjoint)
 (pick:selectFinal T S c.a c.b=some (.remaining bad (.second u v))) :
 ∃R∈rows S c.a c.b bad.c,∃C qa ub,subtree T v=some C ∧
  LiteralProps T S c.a c.b bad u v R C qa ub := by
 obtain ⟨R,Rmem,Rorder,badLocation,Rlabels,Rlocation⟩:=actual_second_bottom_row T S c d bad u v proper early pick
 have finalFacts:=selectFinal_remaining_facts T S c.a c.b bad (.second u v) pick
 have badPick:=finalFacts.2.1
 have front:=actual_front_checks T S c d proper early
 have priority:=actual_rule4_priority_closed T S c d proper early
 have endpoints:=actual_source_endpoint_members T S c d proper early
 have partition:=actual_selected_bad_partition_check T S c d bad proper early badPick
 have embedding:=selected_bad_target_embeddings T S c.a c.b bad front.2.2.2.2.1 badPick
  (actual_target_embeddings T S c d proper early graph)
 have caCore:c.a∈coreLabels S c.a c.b:=endpoint_core (Or.inl rfl) endpoints.1
 have regions0:=selected_second_out_regions T (subtreeLabels S bad.badArc) (coreLabels S c.a c.b)
  bad.c c.a u v priority.1 partition embedding caCore finalFacts.2.2
 have regions:OutRegion T (leaves R.X) u [bad.c] ∧ OutRegion T (leaves R.X) v (coreLabels S c.a c.b) := by
  rw [←Rlabels];exact regions0
 have order:incident T (leaves R.X)=[u,v] ∨ incident T (leaves R.X)=[v,u] := by
  rw [←Rlabels];exact (literal_second_flags T _ bad.c u v finalFacts.2.2).1
 have um:u∈incident T (leaves R.X) := by
  rcases order with eq|eq <;> rw [eq]
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
 have vm:v∈incident T (leaves R.X) := by
  rcases order with eq|eq <;> rw [eq]
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_self
 obtain ⟨C,Clocation⟩:=(incident_spec T (leaves R.X) v).mp vm |>.1
 have Clabels:=source_labels_of_subtree T v C Clocation
 have leafc:=singleton_out_region_leaf T (leaves R.X) bad.c u priority.1 um regions.1
 have members:R.a∈leaves S ∧ R.b∈leaves S ∧ R.b∈coreLabels S c.a c.b := by
  rcases Rorder with ⟨ha,hb⟩|⟨ha,hb⟩
  · rw [ha,hb];exact ⟨endpoints.1,endpoints.2,endpoint_core (Or.inr rfl) endpoints.2⟩
  · rw [ha,hb];exact ⟨endpoints.2,endpoints.1,endpoint_core (Or.inl rfl) endpoints.1⟩
 have aT:R.a∈leaves T:=priority.2.2.1.mem_iff.mpr members.1
 have bT:R.b∈leaves T:=priority.2.2.1.mem_iff.mpr members.2.1
 obtain ⟨qa,leafa⟩:=CutRealization.leaf_exists aT
 obtain ⟨ub,leafb⟩:=CutRealization.leaf_exists bT
 have complement:∀z,z∈leaves T→(z∈leaves C ↔ z∉leaves R.X ∧ z≠bad.c) := by
  intro z zT
  have zS:z∈leaves S:=priority.2.2.1.mem_iff.mp zT
  have core:=selected_bad_core_complement T S c.a c.b bad z front.2.2.2.2.1 badPick zS
  rw [Rlabels] at core
  rw [←Clabels]
  exact (regions.2.2 z zT).trans core
 have bC:R.b∈leaves C := by
  rw [←Clabels];exact (regions.2.2 R.b bT).mpr members.2.2
 have cNotC:bad.c∉leaves C := by
  intro cC
  exact ((complement bad.c (Integration.leafAt_label T u bad.c leafc)).mp cC).2 rfl
 have cherry:∃i∈Universal233.HardParent.vertices T,CherryAt T i R.a R.b ∨ CherryAt T i R.b R.a := by
  obtain ⟨i,location⟩:=cherry_address T c.a c.b (hasCherry_bool_prop T c.a c.b front.2.1)
  have im:i∈Universal233.HardParent.vertices T := by
   rcases location with h|h <;> exact (vertices_correct T i).mpr ⟨_,h⟩
  refine ⟨i,im,?_⟩
  rcases Rorder with ⟨ha,hb⟩|⟨ha,hb⟩
  · simpa only [ha,hb] using location
  · simpa only [ha,hb] using location.symm
 have len:(cuts S R.a R.b).length=2 := by
  rcases Rorder with ⟨ha,hb⟩|⟨ha,hb⟩
  · rw [ha,hb];exact front.2.2.2.2.1
  · rw [ha,hb]
    change (pendantOriginal S c.b c.a).length=2
    rw [pendantOriginal_swap S c.b c.a];exact front.2.2.2.2.1
 exact ⟨R,Rmem,C,qa,ub,Clocation,front.1,Rlocation,cherry,len,complement,bC,cNotC,leafa,leafb,leafc,
  order.symm,regions.2.1.2,regions.1.1.2,regions.2.1.1,regions.1.1.1,Rlabels,Rorder⟩

end PaidBuilderAuthor

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @PaidBuilderAuthor.literal_second_flags
#print axioms PaidBuilderAuthor.literal_second_flags
#check @PaidBuilderAuthor.outside_check_iff
#print axioms PaidBuilderAuthor.outside_check_iff
#check @PaidBuilderAuthor.outside_label_not_both
#print axioms PaidBuilderAuthor.outside_label_not_both
#check @PaidBuilderAuthor.false_paint_outgoing
#print axioms PaidBuilderAuthor.false_paint_outgoing
#check @PaidBuilderAuthor.outside_label_not_selected
#print axioms PaidBuilderAuthor.outside_label_not_selected
#check @PaidBuilderAuthor.selected_second_out_regions
#print axioms PaidBuilderAuthor.selected_second_out_regions
#check @PaidBuilderAuthor.selected_bad_core_complement
#print axioms PaidBuilderAuthor.selected_bad_core_complement
#check @PaidBuilderAuthor.cherry_address
#print axioms PaidBuilderAuthor.cherry_address
#check @PaidBuilderAuthor.tree_has_label
#print axioms PaidBuilderAuthor.tree_has_label
#check @PaidBuilderAuthor.tree_singleton_of_nodup
#print axioms PaidBuilderAuthor.tree_singleton_of_nodup
#check @PaidBuilderAuthor.singleton_out_region_leaf
#print axioms PaidBuilderAuthor.singleton_out_region_leaf
#check @PaidBuilderAuthor.actual_second_literal_props
#print axioms PaidBuilderAuthor.actual_second_literal_props
