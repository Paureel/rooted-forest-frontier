import AdmittedRemainingGood
namespace AdmittedRule5Author
open RMAF Universal233

theorem partition_check_labels_perm (labels labels' : List Nat) (blocks : List (List Nat))
 (order : labels.Perm labels') (check : partitionCheck labels blocks=true) :
 partitionCheck labels' blocks=true := by
 have facts : (blocks.all (fun B=>!B.isEmpty)=true ∧
  labels.all (fun x=>blocks.flatten.count x==1)=true) ∧
  blocks.flatten.all (fun x=>labels.contains x)=true := by
  simpa only [partitionCheck,Bool.and_eq_true] using check
 have cover : labels'.all (fun x=>blocks.flatten.count x==1)=true := by
  apply List.all_eq_true.mpr
  intro x hx
  exact (List.all_eq_true.mp facts.1.2) x (order.mem_iff.mpr hx)
 have inside : blocks.flatten.all (fun x=>labels'.contains x)=true := by
  apply List.all_eq_true.mpr
  intro x hx
  have old:=(List.all_eq_true.mp facts.2) x hx
  exact List.contains_iff_mem.mpr (order.mem_iff.mp (List.contains_iff_mem.mp old))
 simp only [partitionCheck,Bool.and_eq_true]
 exact ⟨⟨facts.1.1,cover⟩,inside⟩

theorem partition_check_blocks_perm (labels : List Nat) (blocks blocks' : List (List Nat))
 (order : blocks.Perm blocks') (check : partitionCheck labels blocks=true) :
 partitionCheck labels blocks'=true := by
 have facts : (blocks.all (fun B=>!B.isEmpty)=true ∧
  labels.all (fun x=>blocks.flatten.count x==1)=true) ∧
  blocks.flatten.all (fun x=>labels.contains x)=true := by
  simpa only [partitionCheck,Bool.and_eq_true] using check
 have flat:=order.flatten
 have nonempty : blocks'.all (fun B=>!B.isEmpty)=true := by
  apply List.all_eq_true.mpr
  intro B hB
  exact (List.all_eq_true.mp facts.1.1) B (order.mem_iff.mpr hB)
 have cover : labels.all (fun x=>blocks'.flatten.count x==1)=true := by
  apply List.all_eq_true.mpr
  intro x hx
  rw [←flat.count_eq x]
  exact (List.all_eq_true.mp facts.1.2) x hx
 have inside : blocks'.flatten.all (fun x=>labels.contains x)=true := by
  apply List.all_eq_true.mpr
  intro x hx
  exact (List.all_eq_true.mp facts.2) x (flat.mem_iff.mpr hx)
 simp only [partitionCheck,Bool.and_eq_true]
 exact ⟨⟨nonempty,cover⟩,inside⟩

theorem disjoint_vertices_symmetric (A B : List Vertex)
 (check : disjointVertices A B=true) : disjointVertices B A=true := by
 apply List.all_eq_true.mpr
 intro b hb
 cases hit:A.contains b with
 | false => rfl
 | true =>
  have hA:=List.contains_iff_mem.mp hit
  have excluded:=(List.all_eq_true.mp check) b hA
  have included : B.contains b=true:=List.contains_iff_mem.mpr hb
  rw [included] at excluded
  cases excluded

theorem pairwise_embeddings_swap_first_two (T : Tree) (X Y C : List Nat)
 (check : pairwiseEmbeddings T [X,Y,C]=true) :
 pairwiseEmbeddings T [Y,X,C]=true := by
 have facts : (disjointVertices (minimalVertices X T) (minimalVertices Y T)=true ∧
  disjointVertices (minimalVertices X T) (minimalVertices C T)=true) ∧
  disjointVertices (minimalVertices Y T) (minimalVertices C T)=true := by
  simpa only [pairwiseEmbeddings,List.all_cons,List.all_nil,Bool.and_eq_true,and_true] using check
 have reverse:=disjoint_vertices_symmetric _ _ facts.1.1
 simp only [pairwiseEmbeddings,List.all_cons,List.all_nil,Bool.and_eq_true,and_true]
 exact ⟨⟨reverse,facts.2⟩,facts.1.2⟩

theorem embeddings_pairwise_iff (T : Tree) (blocks : List (List Nat)) :
 pairwiseEmbeddings T blocks=true ↔
 blocks.Pairwise (fun X Y=>disjointVertices (minimalVertices X T) (minimalVertices Y T)=true) := by
 induction blocks with
 | nil => constructor <;> intro h <;> first |exact .nil |rfl
 | cons B rest ih =>
  simp only [pairwiseEmbeddings,Bool.and_eq_true,List.all_eq_true,List.pairwise_cons,ih]

theorem pairwise_embeddings_perm (T : Tree) (blocks blocks' : List (List Nat))
 (order : blocks.Perm blocks') (check : pairwiseEmbeddings T blocks=true) :
 pairwiseEmbeddings T blocks'=true := by
 apply (embeddings_pairwise_iff T blocks').mpr
 exact ((embeddings_pairwise_iff T blocks).mp check).perm order
  (fun {_ _} h=>disjoint_vertices_symmetric _ _ h)

end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.partition_check_labels_perm
#print axioms AdmittedRule5Author.partition_check_labels_perm
#check @AdmittedRule5Author.partition_check_blocks_perm
#print axioms AdmittedRule5Author.partition_check_blocks_perm
#check @AdmittedRule5Author.disjoint_vertices_symmetric
#print axioms AdmittedRule5Author.disjoint_vertices_symmetric
#check @AdmittedRule5Author.pairwise_embeddings_swap_first_two
#print axioms AdmittedRule5Author.pairwise_embeddings_swap_first_two
#check @AdmittedRule5Author.embeddings_pairwise_iff
#print axioms AdmittedRule5Author.embeddings_pairwise_iff
#check @AdmittedRule5Author.pairwise_embeddings_perm
#print axioms AdmittedRule5Author.pairwise_embeddings_perm
