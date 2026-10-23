import CommonInterfaces
namespace Universal233.Rule5CommonSelector
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Classification Rule5FinalClassification

theorem selected_original_source {T S : Tree} {i q : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (hz : selectFinal T S a b=some (.remaining d (.one q))) :
 ∃u, d.badArc≠[] ∧ subtree S d.badArc=some u ∧ (leaves u).Perm (subtreeLabels S d.badArc) ∧
 d.singletonArc≠[] ∧ d.singletonArc.dropLast∈minimalVertices [a,b] S ∧
 d.singletonArc∉minimalVertices [a,b] S ∧ d.c∈subtreeLabels S d.singletonArc := by
 have sound := final_selected_sound ch ad hz
 have ds := selectBad_sound sound.2.1
 have bad := (cuts_spec S a b d.badArc).1 ds.1
 have single := (cuts_spec S a b d.singletonArc).1 ds.2.1
 obtain ⟨u,hu⟩ := bad.1
 refine ⟨u,bad.2.1,hu,?_,single.2.1,single.2.2.1,single.2.2.2,?_⟩
 · rw [source_subtree_labels hu]
 · rw [source_subtree_labels ds.2.2.2.2]; simp [leaves]

/-- The literal completed source primitive, at the current cut budget. -/
def runCommon (T S : Tree) (a b : Nat) (d : BadSelection) (budget : Nat)
 (cb : Tree→Tree→Nat→Option (List (List Nat))) : Option (Option (List (List Nat))) :=
 OrdinaryCommonSplit.Source.runSource T S (subtreeLabels S d.badArc) (outsideLabels S a b d) d.badArc budget cb

def commonJobs (T S : Tree) (a b : Nat) (d : BadSelection) (budget : Nat) : List OrdinaryCommonSplit.Caller.Job :=
 OrdinaryCommonSplit.Source.sourceJobs T S (subtreeLabels S d.badArc) (outsideLabels S a b d) d.badArc budget

theorem selected_one_nonrefusal {T S : Tree} {i q : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (hz : selectFinal T S a b=some (.remaining d (.one q))) (budget : Nat)
 (cb : Tree→Tree→Nat→Option (List (List Nat))) : ∃answer,runCommon T S a b d budget cb=some answer := by
 have prop := properPair_parts (admitted_parts ad).1
 obtain ⟨pt,ps,et,es,hpT,hpS,good,aY,bY,cY,boundary⟩ := selected_common_checks ch ad hz
 obtain ⟨u,pn,source,labels,rn,rp,ro,below⟩ := selected_original_source ch ad hz
 exact OrdinaryCommonSplit.Source.actual_source_nonrefusal T S u
   (subtreeLabels S d.badArc) (outsideLabels S a b d) (coreLabels S a b)
   d.badArc q d.singletonArc a b d.c budget cb prop.1 prop.2.1 hpT hpS pn source labels boundary
   pt et es good (actual_hasCherry ch) aY bY cY rn rp ro below

theorem selected_one_bounded_solver {T S : Tree} {i q : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (hz : selectFinal T S a b=some (.remaining d (.one q))) (budget : Nat)
 (cb : Tree→Tree→Nat→Option (List (List Nat)))
 (ih : OrdinaryCommonSplit.Source.SourceIH T S (subtreeLabels S d.badArc) (outsideLabels S a b d) d.badArc budget cb) :
 ∃answer,runCommon T S a b d budget cb=some answer ∧ OrdinaryCommonSplit.Caller.BoundedExact T S budget answer := by
 have prop := properPair_parts (admitted_parts ad).1
 obtain ⟨pt,ps,et,es,hpT,hpS,good,aY,bY,cY,boundary⟩ := selected_common_checks ch ad hz
 obtain ⟨u,pn,source,labels,rn,rp,ro,below⟩ := selected_original_source ch ad hz
 exact OrdinaryCommonSplit.Source.actual_source_bounded_solver T S u
   (subtreeLabels S d.badArc) (outsideLabels S a b d) (coreLabels S a b)
   d.badArc q d.singletonArc a b d.c budget cb prop.1 prop.2.1 hpT hpS pn source labels boundary
   pt et es good (actual_hasCherry ch) aY bY cY rn rp ro below ih

theorem selected_one_job_progress (T S : Tree) (a b : Nat) (d : BadSelection) (budget : Nat)
 (j : OrdinaryCommonSplit.Caller.Job) (hj : j∈commonJobs T S a b d budget) :
 DepthOne.proper j.T j.S=true ∧ j.budget<budget ∧ budget-j.budget=1 :=
 OrdinaryCommonSplit.Source.source_job_progress T S (subtreeLabels S d.badArc) (outsideLabels S a b d) d.badArc budget j hj
end Universal233.Rule5CommonSelector
