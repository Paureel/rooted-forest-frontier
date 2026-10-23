import ForestLocalityV2
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open IndependentGeometry IndependentOneExchange ContactedClade ContactedRepair
namespace ContactedSource

theorem merge_append (a b z : Nat) (G H : List (List Nat)) :
 mergeCommon a b z (G++H)=mergeCommon a b z G++mergeCommon a b z H := by
 simp only [mergeCommon,coarsen,List.map_append,List.filter_append]

theorem merge_perm (a b z : Nat) {G H : List (List Nat)} (p : G.Perm H) :
 (mergeCommon a b z G).Perm (mergeCommon a b z H) :=
 ((p.map (shrinkBlock a b z)).filter (fun B : List Nat=>!B.isEmpty)).map (expandBlock a b z)

theorem shrink_fixed (a b z : Nat) (B : List Nat)
 (na : a∉B) (nb : b∉B) : shrinkBlock a b z B=B := by
 unfold shrinkBlock
 have f : B.filter (fun x=>x != b)=B := List.filter_eq_self.2 (fun x hx=>by
  have ne : x≠b := fun eq=>nb (eq ▸ hx)
  simpa only [bne_iff_ne] using ne)
 rw [f]
 clear nb f
 induction B with
 | nil => rfl
 | cons x xs ih =>
  have ne : x≠a := fun eq=>na (eq ▸ List.mem_cons_self)
  have tail : a∉xs := fun hx=>na (List.mem_cons_of_mem x hx)
  have guard : (x==a)=false := by simpa only [beq_eq_false_iff_ne] using ne
  simp only [List.map_cons,guard,Bool.false_eq_true,ite_false,ih tail]

theorem expand_fixed (a b z : Nat) (B : List Nat) (nz : z∉B) : expandBlock a b z B=B := by
 induction B with
 | nil => rfl
 | cons x xs ih =>
  have xz : x≠z := fun eq=>nz (by simp only [List.mem_cons];exact Or.inl eq.symm)
  have tail : z∉xs := fun hx=>nz (List.mem_cons_of_mem x hx)
  have guard : (x==z)=false := by simpa only [beq_eq_false_iff_ne] using xz
  change (if (x==z) then [a,b] else [x])++expandBlock a b z xs=x::xs
  rw [guard,ih tail]
  rfl

theorem merge_fixed (a b z : Nat) (P : List (List Nat))
 (no : ∀B∈P,a∉B ∧ b∉B ∧ z∉B) (ne : ∀B∈P,B≠[]) : mergeCommon a b z P=P := by
 induction P with
 | nil => rfl
 | cons B rest ih =>
  have absent := no B List.mem_cons_self
  have nonempty := ne B List.mem_cons_self
  have tail := ih (fun D hd=>no D (List.mem_cons_of_mem B hd)) (fun D hd=>ne D (List.mem_cons_of_mem B hd))
  have shrink := shrink_fixed a b z B absent.1 absent.2.1
  have expand := expand_fixed a b z B absent.2.2
  have test : (!B.isEmpty)=true := by cases B <;> first | contradiction | rfl
  simp only [mergeCommon,coarsen,List.map_cons,List.filter_cons,shrink,test,ite_true] at tail ⊢
  rw [expand,tail]

theorem merge_core_perm (a b z : Nat) (Y : List Nat) (G : List (List Nat))
 (no : ∀B∈otherForest Y G,a∉B ∧ b∉B ∧ z∉B)
 (ne : ∀B∈otherForest Y G,B≠[]) :
 (mergeCommon a b z G).Perm (mergeCommon a b z (coreForest Y G)++otherForest Y G) := by
 have perm := merge_perm a b z (forest_partition_perm Y G)
 rw [merge_append,merge_fixed a b z _ no ne] at perm
 exact perm

theorem core_fields_lift {T S R Q : Tree} {Y : List Nat} {C : List (List Nat)}
 (rt : restrict Y T=some R) (rs : restrict Y S=some Q)
 (sub : ∀x∈leaves R,x∈Y) (hC : agreement R Q C=true) :
 C.all (restrictionAgrees T S)=true ∧ pairwiseEmbeddings S C=true ∧ ∀B∈C,∀x∈B,x∈Y := by
 have checks := hC
 simp only [agreement,Bool.and_eq_true] at checks
 have labels : ∀B∈C,∀x∈B,x∈Y := fun B hb x hx=>sub x (partition_labels checks.1.1.1.1 B hb x hx)
 refine ⟨?_,?_,labels⟩
 · apply List.all_eq_true.2
   intro B hb
   rw [←restriction_on_core rt rs (labels B hb)]
   exact List.all_eq_true.1 checks.1.1.2 B hb
 · apply (pairwise_iff S C).2
   apply List.Pairwise.imp_of_mem _ ((pairwise_iff Q C).1 checks.2)
   intro A B ha hb old
   exact (hull_disjoint_restrict (labels A ha) (labels B hb) rs).2 old

theorem source_fields_append {T S U : Tree} {p : Vertex} {C P : List (List Nat)}
 (sub : CoreGraph.subtree S p=some U) (nd : (leaves S).Nodup)
 (inside : ∀B∈P,∀x∈B,x∈leaves U) (outside : ∀B∈C,∀x∈B,x∉leaves U)
 (shapeC : C.all (restrictionAgrees T S)=true) (shapeP : P.all (restrictionAgrees T S)=true)
 (hullC : pairwiseEmbeddings S C=true) (hullP : pairwiseEmbeddings S P=true) :
 (C++P).all (restrictionAgrees T S)=true ∧ pairwiseEmbeddings S (C++P)=true := by
 constructor
 · simp only [List.all_append,shapeC,shapeP,Bool.true_and]
 · apply pairwise_append_own S C P hullC hullP
   intro A ha B hb
   apply disjoint_sym
   apply (disjoint_iff _ _).2
   intro v hv hA
   exact clade_span_disjoint sub nd (inside B hb) (fun x hx hxa=>outside A ha x hxa hx)
    v hv (minimal_in_span S A v hA)

theorem source_fields_perm {T S : Tree} {C H : List (List Nat)} (perm : C.Perm H)
 (fields : H.all (restrictionAgrees T S)=true ∧ pairwiseEmbeddings S H=true) :
 C.all (restrictionAgrees T S)=true ∧ pairwiseEmbeddings S C=true := by
 refine ⟨List.all_eq_true.2 (fun B hb=>List.all_eq_true.1 fields.1 B (perm.mem_iff.1 hb)),pairwise_perm perm.symm fields.2⟩
end ContactedSource

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedSource.merge_append
#print axioms ContactedSource.merge_append
#check @ContactedSource.merge_perm
#print axioms ContactedSource.merge_perm
#check @ContactedSource.shrink_fixed
#print axioms ContactedSource.shrink_fixed
#check @ContactedSource.expand_fixed
#print axioms ContactedSource.expand_fixed
#check @ContactedSource.merge_fixed
#print axioms ContactedSource.merge_fixed
#check @ContactedSource.merge_core_perm
#print axioms ContactedSource.merge_core_perm
#check @ContactedSource.core_fields_lift
#print axioms ContactedSource.core_fields_lift
#check @ContactedSource.source_fields_append
#print axioms ContactedSource.source_fields_append
#check @ContactedSource.source_fields_perm
#print axioms ContactedSource.source_fields_perm
