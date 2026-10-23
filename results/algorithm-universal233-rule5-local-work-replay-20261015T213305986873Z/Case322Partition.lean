import Case322Arcs
namespace Universal233.Rule5Case322
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local
set_option maxRecDepth 10000

/-- Literal original-edge partition: each cluster split acts on the current
permanent original-label partition, without suppressing or unioning edges. -/
def arcPartitionFrom (T : Tree) : List RMAF.Vertex → List (List Nat) → List (List Nat)
 | [],P => P
 | q::qs,P => arcPartitionFrom T qs (splitForest P (subtreeLabels T q))
def arcPartition (T : Tree) (qs : List RMAF.Vertex) := arcPartitionFrom T qs [leaves T]

theorem refine_split_unmixed {F P : List (List Nat)} {X : List Nat}
 (nonempty : ∀ B, B ∈ F → B ≠ []) (href : Refines F P)
 (unmixed : ∀ B, B ∈ F → BinaryExchange.mixed B X.contains ≠ true) :
 Refines F (splitForest P X) := by
 intro B hB
 obtain ⟨C,hC,sub⟩ := href B hB
 have mono : (∀ x, x ∈ B → x ∈ X) ∨ (∀ x, x ∈ B → x ∉ X) := by
   by_cases ex : ∃ x, x ∈ B ∧ x ∈ X
   · left
     intro y yB
     apply Classical.byContradiction
     intro yn
     obtain ⟨x,xB,xX⟩ := ex
     exact unmixed B hB ((BinaryExchange.mixed_iff B X.contains).2
       ⟨⟨x,xB,List.contains_iff_mem.2 xX⟩,⟨y,yB,by simpa using yn⟩⟩)
   · right
     intro x xB xX; exact ex ⟨x,xB,xX⟩
 obtain ⟨x,xB⟩ := List.exists_mem_of_ne_nil B (nonempty B hB)
 rcases mono with yes | no
 · let D := BinaryExchange.yes C X.contains
   have xD : x ∈ D := by simp [D,BinaryExchange.yes,sub x xB,yes x xB]
   have neD : D ≠ [] := by intro e; rw [e] at xD; exact List.not_mem_nil xD
   refine ⟨D,List.mem_flatMap.2 ⟨C,hC,(BinaryExchange.mem_split C D X.contains).2 ⟨Or.inl rfl,neD⟩⟩,?_⟩
   intro y yB; simp [D,BinaryExchange.yes,sub y yB,yes y yB]
 · let D := BinaryExchange.no C X.contains
   have xD : x ∈ D := by simp [D,BinaryExchange.no,sub x xB,no x xB]
   have neD : D ≠ [] := by intro e; rw [e] at xD; exact List.not_mem_nil xD
   refine ⟨D,List.mem_flatMap.2 ⟨C,hC,(BinaryExchange.mem_split C D X.contains).2 ⟨Or.inr rfl,neD⟩⟩,?_⟩
   intro y yB; simp [D,BinaryExchange.no,sub y yB,no y yB]

theorem refines_arcPartitionFrom {T : Tree} {F P : List (List Nat)}
 (qs : List RMAF.Vertex) (nonempty : ∀ B, B ∈ F → B ≠ [])
 (href : Refines F P)
 (unmixed : ∀ q, q ∈ qs → ∀ B, B ∈ F → BinaryExchange.mixed B (subtreeLabels T q).contains ≠ true) :
 Refines F (arcPartitionFrom T qs P) := by
 induction qs generalizing P with
 | nil => exact href
 | cons q qs ih =>
   exact ih (refine_split_unmixed nonempty href (unmixed q (by simp)))
     (fun r hr => unmixed r (by simp [hr]))

theorem refines_arcPartition {T S : Tree} {F : List (List Nat)} (qs : List RMAF.Vertex)
 (ha : agreement T S F = true)
 (unmixed : ∀ q, q ∈ qs → ∀ B, B ∈ F → BinaryExchange.mixed B (subtreeLabels T q).contains ≠ true) :
 Refines F (arcPartition T qs) := by
 have hp := (BinaryExchange.agreement_parts T S F ha).1
 apply refines_arcPartitionFrom qs (BinaryExchange.partition_parts _ _ hp).1
 · intro B hB; exact ⟨leaves T,by simp,fun x hx => block_labels hp hB hx⟩
 · exact unmixed

theorem singleton_unmixed {T : Tree} {F : List (List Nat)} {a : Nat}
 (hp : partitionCheck (leaves T) F = true) (single : [a] ∈ F) :
 ∀ B, B ∈ F → BinaryExchange.mixed B [a].contains ≠ true := by
 intro B hB hm
 obtain ⟨⟨x,xB,xa⟩,⟨y,yB,ya⟩⟩ := (BinaryExchange.mixed_iff B [a].contains).1 hm
 have e : x = a := by simpa using xa
 subst x
 have yna : y ≠ a := by simpa using ya
 exact singleton_excludes_other hp single hB yB yna xB

theorem singleton_plus_unused_refines {T S : Tree} {F : List (List Nat)} {a : Nat}
 {qa : RMAF.Vertex} (qs : List RMAF.Vertex) (ha : agreement T S F = true)
 (leafA : LeafAt T qa a) (single : [a] ∈ F)
 (unmixed : ∀ q, q ∈ qs → ∀ B, B ∈ F → BinaryExchange.mixed B (subtreeLabels T q).contains ≠ true) :
 Refines F (arcPartition T (qa::qs)) := by
 apply refines_arcPartition (qa::qs) ha
 intro q hq
 rcases List.mem_cons.1 hq with rfl | hq
 · rw [source_subtree_labels leafA]
   exact singleton_unmixed (BinaryExchange.agreement_parts T S F ha).1 single
 · exact unmixed q hq

end Universal233.Rule5Case322
