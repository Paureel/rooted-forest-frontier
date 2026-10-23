import GenerationBounds
namespace GenericForest.LocalPolynomial
open RMAF ForestState Universal233 Universal233.CoreWork Universal233.CoreProgram Universal233.WholeSourceWork

theorem valid_address_bound (s : Tree) (v : RMAF.Vertex) (valid : CoreGraph.Valid s v) : v.length≤treeNodes s := by
 induction s generalizing v with
 | leaf x =>
  cases v with
  | nil => simp
  | cons b v => obtain ⟨u,hu⟩:=valid;simp [CoreGraph.subtree] at hu
 | node l r ihl ihr =>
  cases v with
  | nil => simp
  | cons b v =>
   obtain ⟨u,hu⟩:=valid
   cases b with
   | false => have h:=ihl v ⟨u,hu⟩;simp only [List.length_cons,treeNodes];omega
   | true => have h:=ihr v ⟨u,hu⟩;simp only [List.length_cons,treeNodes];omega

theorem branch_generated (t : Tree) (ss : List Tree) (h : Overlap) (q : Nat) (io : Nat × Output)
 (mem : io∈branches t ss h q) :
 ∃s,ss[io.1]?=some s ∧ io.2∈(generate s (VertexGeometry.colorLabel t h.vertex) q).outputs := by
 simp only [branches,List.mem_append,List.mem_map] at mem
 rcases mem with ⟨o,mem,eq⟩|⟨o,mem,eq⟩
 all_goals cases eq
 all_goals unfold raw at mem
 all_goals split at mem
 all_goals first | simp at mem | exact ⟨_,by assumption,mem⟩

theorem materialization_bound (t : Tree) (ss : List Tree) (q M : Nat) (h : Overlap)
 (hp : proper (some t) ss=true) (size : (leaves t).length≤M) (budget : q≤M)
 (selected : overlap t ss=some h) (io : Nat × Output) (mem : io∈branches t ss h q) :
 materializationBill t ss q io.1 io.2≤materialCap M := by
 obtain ⟨s,hi,generated⟩:=branch_generated t ss h q io mem
 have source:=source_size_bounds (some t) ss hp M size s (List.mem_of_getElem? hi)
 have nd:=(proper_source_labels t ss hp s (List.mem_of_getElem? hi)).1
 have valid:=Assembly.generated_source_valid s (VertexGeometry.colorLabel t h.vertex) q io.2 generated
 have flat:=(RestrictionBridge.checked_flatten_perm (leaves s) io.2.partition nd valid.1).length_eq
 have real:=CutRealization.generate_original_realization s (VertexGeometry.colorLabel t h.vertex) q io.2 generated
 have cutlength:=SourceCoverage.generate_output_budget s (VertexGeometry.colorLabel t h.vertex) q io.2 generated
 have cells : (io.2.sourceCuts.map List.length).sum≤2*M*M := by
  have sum:=nat_sum_le_constant io.2.sourceCuts List.length (2*M)
   (fun v hv=>Nat.le_trans (valid_address_bound s v (real.2.1 v hv)) source.1)
  have scaled:=Nat.mul_le_mul_right (2*M) (Nat.le_trans cutlength budget)
  have eq : M*(2*M)=2*M*M:=by ac_rfl
  rw [eq] at scaled
  exact Nat.le_trans sum scaled
 have paid:=branch_paid_proper t ss hp h selected q io.1 io.2 mem
 have orig:=inspection_bound (some t) ss q M hp size budget
 have child:=inspection_bound (some t) (replace ss io.1 io.2.partition) (q-io.2.sourceCuts.length) M
  paid.2.2 size (by omega)
 have sourceNodes:=(state_size_bounds (some t) ss hp M size).2.1
 have inner : io.2.partition.flatten.length+(io.2.sourceCuts.map List.length).sum+GenericForest.sourceNodes ss+1≤
  M+2*M*M+2*M+1 := by omega
 have output:=Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left inner 4)
 unfold materializationBill materialCap
 omega

theorem materializations_bound (t : Tree) (ss : List Tree) (q M : Nat) (h : Overlap)
 (hp : proper (some t) ss=true) (size : (leaves t).length≤M) (budget : q≤M) (selected : overlap t ss=some h) :
 ((branches t ss h q).map fun io=>materializationBill t ss q io.1 io.2).sum≤12*materialCap M*2^q := by
 have sum:=nat_sum_le_constant (branches t ss h q) (fun io=>materializationBill t ss q io.1 io.2) (materialCap M)
  (fun io mem=>materialization_bound t ss q M h hp size budget selected io mem)
 have scaled:=Nat.mul_le_mul_right (materialCap M) (branches_output_count t ss h q)
 have eq : (12*2^q)*materialCap M=(12*materialCap M)*2^q:=by ac_rfl
 rw [eq] at scaled
 exact Nat.le_trans sum scaled

theorem jobs_length (t : Tree) (ss : List Tree) (js : List (PaidQueries.Job (Tree × Tree) Forest))
 (hjobs : jobs t ss=some js) : js.length=ss.length := by
 induction ss generalizing js with
 | nil =>
  have eq : js=[]:=by simpa [jobs] using hjobs.symm
  subst js
  rfl
 | cons s ss ih =>
  have step (j : PaidQueries.Job (Tree × Tree) Forest) (h : (jobs t ss).map (j::·)=some js) : js.length=(s::ss).length := by
   obtain ⟨tail,ht,eq⟩:=Option.map_eq_some_iff.1 h
   subst js
   simpa only [List.length_cons] using congrArg Nat.succ (ih tail ht)
  cases pair : componentPair t s with
  | none => simp [jobs,pair] at hjobs
  | some p =>
   cases pre : DepthOne.pretest01 p.1 p.2 with
   | refused => simp [jobs,pair,pre] at hjobs
   | rejected => exact step (.hard p) (by simpa [jobs,pair,pre] using hjobs)
   | found c => exact step (.resolved p (DepthOne.cutCost c) (DepthOne.forest s c)) (by simpa [jobs,pair,pre] using hjobs)
end GenericForest.LocalPolynomial
