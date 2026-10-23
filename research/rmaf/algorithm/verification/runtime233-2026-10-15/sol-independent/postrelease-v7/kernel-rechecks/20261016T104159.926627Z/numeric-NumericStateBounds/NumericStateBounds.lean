import NumericSizes
namespace OrdinaryDispatch.GlobalNumeric
open RMAF ForestState Universal233 Universal233.CoreWork
open Universal233.WholeSourceWork
open GenericForest.CheckCorrespondence GenericForest.LocalPolynomial

/-- Proper forest states have no new labels; the equality is source sum, not
just a separate cap on each component. Includes the proper empty state. -/
theorem proper_forest_caps (target : Option Tree) (ss : List Tree) (N M : Nat)
 (hp : proper target ss=true) (size : (labels target).length≤N)
 (cap : ∀x,x∈labels target→x≤M) :
 GenericForest.targetNodes target≤2*N ∧ GenericForest.sourceNodes ss≤2*N ∧ ss.length≤2*N ∧
 (ss.map leaves).flatten.length≤N ∧
 (∀s,s∈ss→treeNodes s≤2*N ∧ (leaves s).length≤N ∧ TreeCap M s ∧
  ∀v,CoreGraph.Valid s v→v.length≤2*N) := by
 have sizes:=state_size_bounds target ss hp N size
 have parts:=proper_parts target ss hp
 have perm:=RestrictionBridge.checked_flatten_perm (labels target) (ss.map leaves) parts.1 parts.2
 refine ⟨sizes.1,sizes.2.1,sizes.2.2,by have:=perm.length_eq;omega,?_⟩
 intro s hs
 have nodes:=source_size_bounds target ss hp N size s hs
 have support : ∀x,x∈leaves s→x∈labels target := by
  intro x hx
  apply perm.mem_iff.1
  exact List.mem_flatten.2 ⟨leaves s,List.mem_map.2 ⟨s,hs,rfl⟩,hx⟩
 exact ⟨nodes.1,nodes.2,fun x hx=>cap x (support x hx),
   fun v hv=>Nat.le_trans (valid_address_bound s v hv) nodes.1⟩

/-- One actual forest recursion edge retains the target and its label domain,
and strictly decreases the original residual budget. -/
theorem forest_edge_caps (t : Tree) (ss : List Tree) (h : GenericForest.Overlap) (q : Nat)
 (hp : proper (some t) ss=true) (selected : GenericForest.overlap t ss=some h)
 (io : Nat×Universal233.CoreProgram.Output) (mem : io∈GenericForest.branches t ss h q) :
 q-io.2.sourceCuts.length<q ∧
 proper (some t) (GenericForest.replace ss io.1 io.2.partition)=true := by
 have edge:=GenericForest.branch_paid_proper t ss hp h selected q io.1 io.2 mem
 exact ⟨by omega,edge.2.2⟩

/-- Overapproximation of exactly the repeated forest-call arm: its index is
the number of literal paid forest replacement edges after an actual entry.
The properness and numeric caps are conclusions, not fields of this relation. -/
inductive ForestDesc (target : Option Tree) (ss0 : List Tree) (q0 : Nat) : Nat→List Tree→Nat→Prop where
 | root : ForestDesc target ss0 q0 0 ss0 q0
 | next {d ss q t h io} : ForestDesc target ss0 q0 d ss q → target=some t →
   GenericForest.overlap t ss=some h → io∈GenericForest.branches t ss h q →
   ForestDesc target ss0 q0 (d+1) (GenericForest.replace ss io.1 io.2.partition) (q-io.2.sourceCuts.length)

theorem forest_desc_invariant (target : Option Tree) (ss0 : List Tree) (q0 N M : Nat)
 (hp0 : proper target ss0=true) (size : (labels target).length≤N)
 (cap : ∀x,x∈labels target→x≤M) {d ss q} (path : ForestDesc target ss0 q0 d ss q) :
 proper target ss=true ∧ d+q≤q0 ∧ GenericForest.targetNodes target≤2*N ∧
 GenericForest.sourceNodes ss≤2*N ∧ ss.length≤2*N ∧ (ss.map leaves).flatten.length≤N ∧
 (∀s,s∈ss→treeNodes s≤2*N ∧ (leaves s).length≤N ∧ TreeCap M s ∧
  ∀v,CoreGraph.Valid s v→v.length≤2*N) := by
 have core : proper target ss=true ∧ d+q≤q0 := by
  induction path with
  | root => exact ⟨hp0,by omega⟩
  | @next d ss q t h io prev eq selected mem ih =>
   have hp : proper (some t) ss=true := by rw [←eq];exact ih.1
   have step:=forest_edge_caps t ss h q hp selected io mem
   exact ⟨by rw [eq];exact step.2,by omega⟩
 exact ⟨core.1,core.2,proper_forest_caps target ss N M core.1 size cap⟩

/-- Bounds all EIGHT restricted/marked trees materialized by the actual common
builder, including outside-only trees that never enter the ordinary trace. -/
theorem common_builder_caps (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex)
 (d : OrdinaryCommonSplit.Caller.Setup)
 (build : OrdinaryCommonSplit.Source.buildSetup T S X Y p=some d) (N M : Nat)
 (sizes : (leaves T).length≤N ∧ (leaves S).length≤N) (cap : PairCap M T S) :
 d.rho≤M+2 ∧ d.gamma≤M+2 ∧
 ∀u,u∈[d.tx,d.sx,d.ty,d.sy,d.mxT,d.mxS,d.myT,d.myS]→
 (leaves u).length≤N ∧ treeNodes u≤2*N ∧ TreeCap (M+2) u := by
 have ident:=OrdinaryCommonSplit.Source.buildSetup_identity T S X Y p d build
 have fresh:=Rule5LocalWork.build_fresh T S X Y p d build
 have maximum:=pair_max_le cap
 have fr : d.rho≤M+2 := by omega
 have fg : d.gamma≤M+2 := by omega
 have ct : TreeCap (M+2) d.T := by rw [ident.1];exact treeCap_mono cap.1 (by omega)
 have cs : TreeCap (M+2) d.S := by rw [ident.2.1];exact treeCap_mono cap.2 (by omega)
 have tx : d.x∈leaves d.T := SourceCoverage.partitionCheck_subset _ _ d.hpT (by simp [d.hx])
 have ty : d.y∈leaves d.T := SourceCoverage.partitionCheck_subset _ _ d.hpT (by simp [d.hy])
 have sx : d.x∈leaves d.S := SourceCoverage.partitionCheck_subset _ _ d.hpS (by simp [d.hx])
 have sy : d.y∈leaves d.S := SourceCoverage.partitionCheck_subset _ _ d.hpS (by simp [d.hy])
 have dt : (leaves d.T).length≤N := by rw [ident.1];exact sizes.1
 have ds : (leaves d.S).length≤N := by rw [ident.2.1];exact sizes.2
 have restricted {A U : Tree} {B : List Nat} (nd : (leaves A).Nodup)
  (hr : restrict B A=some U) (sz : (leaves A).length≤N) (cp : TreeCap (M+2) A) :
  (leaves U).length≤N ∧ treeNodes U≤2*N ∧ TreeCap (M+2) U := by
  have size:=Nat.le_trans (Rule5ActualTrace.restricted_size nd hr) sz
  have nodes:=treeNodes_le_twice_leaves U
  exact ⟨size,by omega,Rule5LocalWork.restrict_numeric hr _ cp⟩
 have marked {A U : Tree} {B : List Nat} {x z : Nat} (nd : (leaves A).Nodup)
  (hr : OrdinaryCommonSplit.marked A B x z=some U) (sz : (leaves A).length≤N)
  (cp : TreeCap (M+2) A) (cx : x≤M+2) (cz : z≤M+2) :
  (leaves U).length≤N ∧ treeNodes U≤2*N ∧ TreeCap (M+2) U := by
  have size:=Nat.le_trans (Rule5ActualTrace.marked_size nd hr) sz
  have nodes:=treeNodes_le_twice_leaves U
  exact ⟨size,by omega,Rule5LocalWork.marked_numeric hr _ cp cx cz⟩
 refine ⟨fr,fg,?_⟩
 intro u hu
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
 rcases hu with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · exact restricted d.nt d.htx dt ct
 · exact restricted d.ns d.hsx ds cs
 · exact restricted d.nt d.hty dt ct
 · exact restricted d.ns d.hsy ds cs
 · exact marked d.nt d.hMXT dt ct (ct _ ty) fr
 · exact marked d.ns d.hMXS ds cs (cs _ sy) fr
 · exact marked d.nt d.hMYT dt ct (ct _ tx) fg
 · exact marked d.ns d.hMYS ds cs (cs _ sx) fg
end OrdinaryDispatch.GlobalNumeric
