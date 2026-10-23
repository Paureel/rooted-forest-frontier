import PendantAntichainR3
open RMAF ForestState OutputState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentGeometry IndependentOneExchange ContactedClade ContactedRepair ContactedSource
namespace ContactedForward

theorem restrict_all_own (T : Tree) (A : List Nat) (keep : ∀x∈leaves T,x∈A) : restrict A T=some T := by
 induction T with
 | leaf x =>
  have yes := List.contains_iff_mem.2 (keep x List.mem_cons_self)
  change (if A.contains x then some (Tree.leaf x) else none)=some (Tree.leaf x)
  rw [yes];rfl
 | node l r il ir =>
  change merge (restrict A l) (restrict A r)=some (.node l r)
  rw [il (fun x hx=>keep x (List.mem_append_left _ hx)),ir (fun x hx=>keep x (List.mem_append_right _ hx))]
  rfl

theorem whole_self_agreement (S : Tree) (nd : (leaves S).Nodup) : agreement S S [leaves S]=true := by
 have ne : leaves S≠[] := by obtain ⟨x,hx⟩ := leaf_witness S;intro eq;rw [eq] at hx;cases hx
 have flat : ([leaves S] : List (List Nat)).flatten.Perm (leaves S) := by
  simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using List.Perm.refl (leaves S)
 have part := IndependentCommon.partition_from_flatten _ _ nd
  (fun B hb=>by have eq : B=leaves S := List.mem_singleton.1 hb;exact eq ▸ ne) flat
 have shape : restrictionAgrees S S (leaves S)=true := by
  unfold restrictionAgrees
  rw [restrict_all_own S (leaves S) (fun _ h=>h)]
  exact iso_same (iso_refl S)
 simp only [agreement,Bool.and_eq_true,List.all_cons,List.all_nil,Bool.and_true]
 exact ⟨⟨⟨⟨part,part⟩,shape⟩,rfl⟩,rfl⟩

theorem agreement_perm_own {T S : Tree} {F G : List (List Nat)} (proper : DepthOne.proper T S=true)
 (perm : F.Perm G) (hF : agreement T S F=true) : agreement T S G=true := by
 obtain ⟨nt,ns,ts⟩ := IndependentReconstruction.proper_parts proper
 have old := hF
 simp only [agreement,Bool.and_eq_true] at old ⊢
 have flat := (perm.flatten.symm).trans (IndependentCommon.flatten_from_partition _ F nt old.1.1.1.1)
 have ne : ∀B∈G,B≠[] := fun B hb=>partition_nonempty old.1.1.1.1 B (perm.mem_iff.2 hb)
 have pt := IndependentCommon.partition_from_flatten _ _ nt ne flat
 have ps := IndependentCommon.partition_from_flatten _ _ ns ne (flat.trans ts)
 have shapes := List.all_eq_true.2 (fun B hb=>List.all_eq_true.1 old.1.1.2 B (perm.mem_iff.2 hb))
 exact ⟨⟨⟨⟨pt,ps⟩,shapes⟩,pairwise_perm perm old.1.2⟩,pairwise_perm perm old.2⟩

theorem split_outside_block (X B : List Nat) (ne : B≠[]) (outside : ∀x∈B,x∉X) : splitBlock X B=[B] := by
 have none : B.filter X.contains=[] := List.filter_eq_nil_iff.2 (fun x hx=>by
  simpa only [←Bool.not_eq_true,List.contains_iff_mem] using outside x hx)
 have all : B.filter (fun x=>!X.contains x)=B := List.filter_eq_self.2 (fun x hx=>by
  simpa only [Bool.not_eq_true',←Bool.not_eq_true,List.contains_iff_mem] using outside x hx)
 have flag : (!B.isEmpty)=true := by cases B <;> first | contradiction | rfl
 simp only [splitBlock,none,all,List.filter_cons,List.filter_nil,List.isEmpty_nil,Bool.not_true,flag,
  Bool.false_eq_true,ite_false,ite_true]

theorem split_outside_forest (X : List Nat) (F : List (List Nat))
 (ne : ∀B∈F,B≠[]) (outside : ∀B∈F,∀x∈B,x∉X) : splitForest X F=F := by
 induction F with
 | nil => rfl
 | cons B rest ih =>
  have tail := ih (fun D hd=>ne D (List.mem_cons_of_mem B hd))
   (fun D hd=>outside D (List.mem_cons_of_mem B hd))
  change splitBlock X B++splitForest X rest=B::rest
  rw [split_outside_block X B (ne B List.mem_cons_self) (outside B List.mem_cons_self),tail]
  rfl

theorem literal_source_agreement (S : Tree) (C : List Vertex) (nd : (leaves S).Nodup)
 (distinct : C.Nodup)
 (actual : ∀p∈C,∃U,CoreGraph.subtree S p=some U)
 (disjoint : ∀p∈C,∀q∈C,p≠q→∀x∈subtreeLabels S p,x∉subtreeLabels S q)
 (anchor : ∃a,a∈leaves S ∧ ∀p∈C,a∉subtreeLabels S p) :
 agreement S S (Rule4.literalPartition S C)=true := by
 have proper : DepthOne.proper S S=true := by
  simpa only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using And.intro nd (And.intro nd (List.Perm.refl _))
 induction C with
 | nil =>
  have eq : Rule4.literalPartition S []=[leaves S] := by
   simp only [Rule4.literalPartition,List.map_nil,List.nil_append,List.all_nil]
   rw [List.filter_eq_self.2 (fun _ _=>rfl)]
  rw [eq];exact whole_self_agreement S nd
 | cons p ps ih =>
  have np := List.nodup_cons.1 distinct
  obtain ⟨U,sub⟩ := actual p List.mem_cons_self
  let X := leaves U
  let Y := (leaves S).filter (fun x=>ps.all (fun q=>!(subtreeLabels S q).contains x))
  let Z := (leaves S).filter (fun x=>!X.contains x && ps.all (fun q=>!(subtreeLabels S q).contains x))
  have sourceX : subtreeLabels S p=X := subtree_labels_lookup sub
  have tailAF := ih np.2 (fun q hq=>actual q (List.mem_cons_of_mem p hq))
   (fun q hq r hr ne=>disjoint q (List.mem_cons_of_mem p hq) r (List.mem_cons_of_mem p hr) ne)
   (by obtain ⟨a,ha,no⟩ := anchor;exact ⟨a,ha,fun q hq=>no q (List.mem_cons_of_mem p hq)⟩)
  have noX : ∀q∈ps,∀x∈subtreeLabels S q,x∉X := by
   intro q hq x hx xp
   have different : q≠p := fun eq=>np.1 (eq ▸ hq)
   rw [←sourceX] at xp
   exact disjoint q (List.mem_cons_of_mem p hq) p List.mem_cons_self different x hx xp
  have xTail : ∀x∈X,ps.all (fun q=>!(subtreeLabels S q).contains x)=true := by
   intro x hx
   apply List.all_eq_true.2
   intro q hq
   have no : x∉subtreeLabels S q := by
    intro xq;exact noX q hq x xq hx
   simpa only [Bool.not_eq_true',←Bool.not_eq_true,List.contains_iff_mem] using no
  have first : Y.filter X.contains=X := by
   have commute : Y.filter X.contains=((leaves S).filter X.contains).filter (fun x=>ps.all (fun q=>!(subtreeLabels S q).contains x)) := by
    simp only [Y,List.filter_filter]
    congr 1;funext x;exact Bool.and_comm _ _
   rw [commute,ContactedOneConsumer.clade_filter sub nd]
   exact List.filter_eq_self.2 xTail
  have rest : Y.filter (fun x=>!X.contains x)=Z := by
   simp only [Y,Z,List.filter_filter,List.flatten_cons,List.flatten_nil,List.append_nil,sourceX]

  have xn : X≠[] := by obtain ⟨x,hx⟩ := leaf_witness U;intro eq;change leaves U=[] at eq;rw [eq] at hx;cases hx
  have zn : Z≠[] := by
   obtain ⟨a,ha,no⟩ := anchor
   have az : a∈Z := by
    apply List.mem_filter.2
    refine ⟨ha,?_⟩
    simp only [Bool.and_eq_true]
    rw [←sourceX]
    exact ⟨by simpa only [Bool.not_eq_true',←Bool.not_eq_true,List.contains_iff_mem] using no p List.mem_cons_self,
     List.all_eq_true.2 (fun q hq=>by simpa only [Bool.not_eq_true',←Bool.not_eq_true,List.contains_iff_mem] using no q (List.mem_cons_of_mem p hq))⟩
   intro eq;rw [eq] at az;cases az
  have flagX : (!X.isEmpty)=true := by cases hx : X with
   | nil => exact False.elim (xn hx)
   | cons x xs => rfl
  have flagZ : (!Z.isEmpty)=true := by cases hz : Z with
   | nil => exact False.elim (zn hz)
   | cons x xs => rfl
  have splitY : splitBlock X Y=[X,Z] := by
   simp only [splitBlock,first,rest,List.filter_cons,List.filter_nil,flagX,flagZ,ite_true]
  have unchanged : (ps.map (subtreeLabels S)).flatMap (splitBlock X)=ps.map (subtreeLabels S) := by
   apply split_outside_forest X _
   · intro B hb
     obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hb
     obtain ⟨V,sv⟩ := actual q (List.mem_cons_of_mem p hq)
     rw [subtree_labels_lookup sv]
     obtain ⟨x,hx⟩ := leaf_witness V
     intro eq;rw [eq] at hx;cases hx
   · intro B hb
     obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hb
     exact noX q hq
  have exactSplit : splitForest X (Rule4.literalPartition S ps)=ps.map (subtreeLabels S)++[X,Z] := by
   simp only [Rule4.literalPartition,IndependentOneExchange.splitForest,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,unchanged]
   change ps.map (subtreeLabels S)++splitBlock X Y=_
   rw [splitY]
  have output : Rule4.literalPartition S (p::ps)=X::(ps.map (subtreeLabels S)++[Z]) := by
   simp only [Rule4.literalPartition,List.map_cons,sourceX,List.cons_append,List.all_cons,Z]
  have after := original_clade_split_agreement S S U p (Rule4.literalPartition S ps) proper sub tailAF
  rw [exactSplit] at after
  rw [output]
  exact agreement_perm_own proper List.perm_middle after

end ContactedForward

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedForward.restrict_all_own
#print axioms ContactedForward.restrict_all_own
#check @ContactedForward.whole_self_agreement
#print axioms ContactedForward.whole_self_agreement
#check @ContactedForward.agreement_perm_own
#print axioms ContactedForward.agreement_perm_own
#check @ContactedForward.split_outside_block
#print axioms ContactedForward.split_outside_block
#check @ContactedForward.split_outside_forest
#print axioms ContactedForward.split_outside_forest
#check @ContactedForward.literal_source_agreement
#print axioms ContactedForward.literal_source_agreement
