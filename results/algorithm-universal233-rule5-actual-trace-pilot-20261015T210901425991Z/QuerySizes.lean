import UniformMass
namespace Universal233.Rule5ActualTrace
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent RestrictionBridge
open CherryBranching Rule5Local Rule5Classification Rule5FinalClassification
open Rule5SourceOrientation Rule5OrdinaryDispatch GenericForest.FrontierWork

theorem restricted_size {T U : Tree} {L : List Nat} (nd : (leaves T).Nodup) (hr : restrict L T=some U) :
 (leaves U).length≤(leaves T).length := by
 have sub : leaves U⊆leaves T := fun x hx => ((restricted_labels_exact T U L hr).1 hx).1
 exact (restricted_nodup T U L hr nd).length_le_of_subset sub

theorem marked_size {T U : Tree} {X : List Nat} {y rho : Nat}
 (nd : (leaves T).Nodup) (marked : OrdinaryCommonSplit.marked T X y rho=some U) :
 (leaves U).length≤(leaves T).length := by
 unfold OrdinaryCommonSplit.marked at marked
 obtain ⟨V,hr,eq⟩ := Option.map_eq_some_iff.1 marked
 rw [←eq,OrdinaryCommonSplit.leaves_relabel,List.length_map]
 exact restricted_size nd hr

theorem setup_job_size (d : OrdinaryCommonSplit.Caller.Setup) (q : Nat)
 {j : OrdinaryCommonSplit.Caller.Job} (mem : j∈OrdinaryCommonSplit.Caller.paidJobs d q) :
 (leaves j.T).length≤(leaves d.T).length ∧ (leaves j.S).length≤(leaves d.S).length := by
 unfold OrdinaryCommonSplit.Caller.paidJobs at mem
 split at mem
 · simp at mem
 · have cases : j=⟨d.tx,d.sx,q-1⟩ ∨ j=⟨d.mxT,d.mxS,q-1⟩ := by simpa using mem
   rcases cases with rfl|rfl
   · exact ⟨restricted_size d.nt d.htx,restricted_size d.ns d.hsx⟩
   · exact ⟨marked_size d.nt d.hMXT,marked_size d.ns d.hMXS⟩

theorem common_job_size (actual : Ordinary) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat)
 {j : OrdinaryCommonSplit.Caller.Job} (mem : j∈(commonTrace actual T S a b d q).calls) :
 (leaves j.T).length≤(leaves T).length ∧ (leaves j.S).length≤(leaves S).length := by
 rw [common_calls] at mem
 unfold Rule5CommonSelector.commonJobs OrdinaryCommonSplit.Source.sourceJobs at mem
 cases build : OrdinaryCommonSplit.Source.buildSetup T S (subtreeLabels S d.badArc)
     (Rule5CommonSelector.outsideLabels S a b d) d.badArc with
 | none => simp [build] at mem
 | some setup =>
   have ident := OrdinaryCommonSplit.Source.buildSetup_identity T S (subtreeLabels S d.badArc)
     (Rule5CommonSelector.outsideLabels S a b d) d.badArc setup build
   have paid : j∈OrdinaryCommonSplit.Caller.paidJobs setup q := by
     simpa only [build] using mem
   have size := setup_job_size setup q paid
   simpa [ident.1,ident.2.1] using size

theorem common_query_size (actual : Ordinary) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat)
 {p : Tree×Tree} {r : Nat} (mem : (p,r)∈directQueries (commonTrace actual T S a b d q).calls) :
 (leaves p.1).length≤(leaves T).length ∧ (leaves p.2).length≤(leaves S).length := by
 obtain ⟨j,hj,eq⟩ := List.mem_map.1 mem
 have size := common_job_size actual T S a b d q hj
 cases eq
 exact size

theorem forest_query_bounds (actual : Ordinary) {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {z : FinalSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) (sel : selectFinal T S a b=some z) (q : Nat)
 {p : Tree×Tree} {r : Nat}
 (mem : (p,r)∈queries actual (.forestJobs (forestJobs T q (selectedForestChildren S a b z)))) :
 r<q ∧ DepthOne.proper p.1 p.2=true ∧
 (leaves p.1).length≤(leaves T).length ∧ (leaves p.2).length≤(leaves T).length := by
 obtain ⟨j,hj,query⟩ := List.mem_flatMap.1 mem
 obtain ⟨hc,target,sources,rem⟩ := literal_job_binding hj
 rw [target,sources] at query
 have prop := selected_child_proper ch ad sel hc
 have valid := frontier_queries_proper actual (some T) j.child.sourceForest j.residual prop p r query
 have size := GenericForest.FrontierSize.frontier_query_size actual (some T) j.child.sourceForest j.residual prop p r query
 have strict := (selected_forest_job_binding ch ad sel hj).2.2.2.2.1
 exact ⟨by omega,valid.2,size⟩

theorem paid_query_bounds (actual : Ordinary) {T S : Tree} {a b : Nat}
 {R : Rule5PaidSelector.SelectedPaid T S} (built : Rule5PaidSelector.buildSelected T S a b=some R)
 (sameLen : (leaves S).length=(leaves T).length) (q : Nat) {p : Tree×Tree} {r : Nat}
 (mem : (p,r)∈queries actual (.paidRequests (Rule5PaidSelector.requests R.geometry q))) :
 r<q ∧ DepthOne.proper p.1 p.2=true ∧
 (leaves p.1).length≤(leaves T).length ∧ (leaves p.2).length≤(leaves T).length := by
 obtain ⟨j,hj,query⟩ := List.mem_flatMap.1 mem
 have actualQuery := (currentFrontier_member query).2.2
 have binding := second_request_binding built hj
 have proper := binding.2.2
 have valid := frontier_queries_proper actual (some j.target) j.sources j.residual proper p r actualQuery
 have size := GenericForest.FrontierSize.frontier_query_size actual (some j.target) j.sources j.residual proper p r actualQuery
 obtain ⟨c,hc,request⟩ := List.mem_filterMap.1 hj
 obtain ⟨aff,branch,target,sources,residual⟩ := Rule5PaidSelector.requestFor_binding request
 have targetSize : (leaves j.target).length=(leaves T).length := by
   rw [target]
   unfold Rule5PaidSelector.opposite
   split
   · rfl
   · exact sameLen
 simp only [ForestState.labels] at size
 rw [targetSize] at size
 exact ⟨by have strict:=binding.1;omega,valid.2,size⟩

theorem selected_query_bounds (actual : Ordinary) {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) {z : FinalSelection}
 (sel : selectFinal T S a b=some z) (q : Nat) {p : Tree×Tree} {r : Nat}
 (mem : (p,r)∈queries actual (selectedTrace actual T S a b q z).calls) :
 r<q ∧ DepthOne.proper p.1 p.2=true ∧
 (leaves p.1).length≤(leaves T).length ∧ (leaves p.2).length≤(leaves T).length := by
 have prop := properPair_parts (admitted_parts ad).1
 have sameLen : (leaves S).length=(leaves T).length := by
   have perm := ((DepthOne.proper_iff T S).1 (admitted_parts ad).1).2.2
   exact perm.length_eq.symm
 cases z with
 | «prefix» s => exact forest_query_bounds actual ch ad sel q mem
 | remaining d z =>
   cases z with
   | first u v => exact forest_query_bounds actual ch ad sel q mem
   | third u v => exact forest_query_bounds actual ch ad sel q mem
   | one edge =>
     have valid := common_direct_progress actual T S a b d q mem
     have size := common_query_size actual T S a b d q mem
     exact ⟨valid.2.1,valid.1,size.1,by rw [←sameLen];exact size.2⟩
   | second u v =>
     cases built : Rule5PaidSelector.buildSelected T S a b with
     | none => simp [selectedTrace,built,queries] at mem
     | some R =>
       apply paid_query_bounds actual built sameLen q
       simpa [selectedTrace,built] using mem

theorem dispatch_query_bounds (actual : Ordinary) {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) (q : Nat) {p : Tree×Tree} {r : Nat}
 (mem : (p,r)∈queries actual (dispatchTrace actual T S a b q).calls) :
 r<q ∧ DepthOne.proper p.1 p.2=true ∧
 (leaves p.1).length≤(leaves T).length ∧ (leaves p.2).length≤(leaves T).length := by
 obtain ⟨z,sel,_⟩ := final_classification_complete ch ad
 apply selected_query_bounds actual ch ad sel q
 simpa [dispatchTrace,sel] using mem

theorem dispatch_potential (actual : Ordinary) {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) (q : Nat) {p : Tree×Tree} {r : Nat}
 (mem : (p,r)∈queries actual (dispatchTrace actual T S a b q).calls) :
 (leaves p.1).length≤(leaves T).length+2 ∧
 (leaves p.1).length+2*r≤(leaves T).length+2*q ∧
 (leaves p.2).length+2*r≤(leaves T).length+2*q := by
 have bound := dispatch_query_bounds actual ch ad q mem
 omega
end Universal233.Rule5ActualTrace
