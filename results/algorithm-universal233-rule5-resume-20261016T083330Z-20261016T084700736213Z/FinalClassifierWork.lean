import OutsideClassifierWork
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork CherryBranching Rule5Classification Rule5FinalClassification

def localTailMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt (Option LocalSelection) :=
 let l:=selectLargeMeter fee T S a b
 match l.value with
 | some e=>⟨some (.large e),l.work+2,l.calls⟩
 | none=>let t:=selectSizeTwoMeter fee T S a b
  match t.value with
  | some c=>⟨some (.two c),l.work+t.work+l.calls.length+3,l.calls++t.calls⟩
  | none=>let o:=selectOutsideMeter fee T S a b
   ⟨some (match o.value with | some c=>.outside c | none=>.remaining),
    l.work+t.work+o.work+l.calls.length+t.calls.length+5,l.calls++(t.calls++o.calls)⟩

def localMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt (Option LocalSelection) :=
 let ad:=admittedMeter fee T S a b
 if ad.value then let r:=localTailMeter fee T S a b
  ⟨r.value,ad.work+r.work+ad.calls.length+2,ad.calls++r.calls⟩
 else ⟨none,ad.work+1,ad.calls⟩

theorem local_value (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) :
 (localMeter fee T S a b).value=selectLocal T S a b := by
 simp only [localMeter,localTailMeter,selectLocal,admitted_value,select_large_value,select_size_two_value,select_outside_value]
 split
 · split <;> (try split) <;> (try split) <;> simp_all
 · rfl

def localTailBudget (n K : Nat) :=selectLargeBudget n K+selectSizeTwoBudget n K+selectOutsideBudget n K+4*n+5
def localBudget (nt ns K : Nat) :=admittedBudget nt ns K+localTailBudget ns K+2*ns+5

theorem local_tail_work (fee : CheckRequest→Nat) (T S : Tree) (a b L K : Nat)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 (primitive : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r →fee r≤K) :
 (localTailMeter fee T S a b).work≤localTailBudget (leaves S).length K := by
 have l:=select_large_work fee T S a b L K tlabs slabs primitive
 have t:=select_size_two_work fee T S a b L K tlabs slabs primitive
 have o:=select_outside_work fee T S a b L K tlabs slabs primitive
 have c:=prefix_selector_calls fee T S a b ((leaves T).length+(leaves S).length) L (by omega) (by omega) tlabs slabs
 simp only [localTailMeter]
 split
 · dsimp only;unfold localTailBudget;omega
 · split <;> dsimp only <;> unfold localTailBudget <;> omega

theorem local_work (fee : CheckRequest→Nat) (T S : Tree) (a b L K : Nat)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 (primitive : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r →fee r≤K) :
 (localMeter fee T S a b).work≤localBudget (leaves T).length (leaves S).length K := by
 have ad:=admitted_work fee T S a b L K tlabs slabs primitive
 have t:=local_tail_work fee T S a b L K tlabs slabs primitive
 have c:=admitted_call_count_polynomial fee T S a b
 simp only [localMeter]
 split <;> dsimp only <;> unfold localBudget <;> omega

theorem local_tail_call_count (fee : CheckRequest→Nat) (T S : Tree) (a b N L : Nat)
 (tcap : (leaves T).length≤N) (scap : (leaves S).length≤N)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L) :
 (localTailMeter fee T S a b).calls.length≤5*(leaves S).length := by
 have c:=prefix_selector_calls fee T S a b N L tcap scap tlabs slabs
 have o:=select_outside_call_count fee T S a b
 simp only [localTailMeter]
 split <;> (try split) <;> simp only [List.length_append] <;> omega

theorem local_call_count (fee : CheckRequest→Nat) (T S : Tree) (a b N L : Nat)
 (tcap : (leaves T).length≤N) (scap : (leaves S).length≤N)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L) :
 (localMeter fee T S a b).calls.length≤7*(leaves S).length+3 := by
 have ad:=admitted_call_count_polynomial fee T S a b
 have tail:=local_tail_call_count fee T S a b N L tcap scap tlabs slabs
 simp only [localMeter]
 split <;> simp only [List.length_append] <;> omega

theorem local_tail_calls (fee : CheckRequest→Nat) (T S : Tree) (a b N L : Nat)
 (tcap : (leaves T).length≤N) (scap : (leaves S).length≤N)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 {r : CheckRequest} (mem : r∈(localTailMeter fee T S a b).calls) : CheckDomain N L r := by
 have c:=prefix_selector_calls fee T S a b N L tcap scap tlabs slabs
 have o:=select_outside_calls fee T S a b N L tcap scap tlabs slabs (r:=r)
 simp only [localTailMeter] at mem
 split at mem
 · exact c.2.2.1 r mem
 · split at mem
   · rcases List.mem_append.1 mem with h|h
     · exact c.2.2.1 r h
     · exact c.2.2.2 r h
   · rcases List.mem_append.1 mem with h|h
     · exact c.2.2.1 r h
     · rcases List.mem_append.1 h with h|h
       · exact c.2.2.2 r h
       · exact o h

theorem local_calls (fee : CheckRequest→Nat) (T S : Tree) (a b N L : Nat)
 (tcap : (leaves T).length≤N) (scap : (leaves S).length≤N)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 {r : CheckRequest} (mem : r∈(localMeter fee T S a b).calls) : CheckDomain N L r := by
 simp only [localMeter] at mem
 split at mem
 · rcases List.mem_append.1 mem with h|h
   · exact admitted_check_domain fee T S a b N L tcap scap tlabs slabs h
   · exact local_tail_calls fee T S a b N L tcap scap tlabs slabs h
 · exact admitted_check_domain fee T S a b N L tcap scap tlabs slabs mem

def finalMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt (Option FinalSelection) :=
 let l:=localMeter fee T S a b
 match l.value with
 | none=>⟨none,l.work+1,l.calls⟩
 | some .remaining=>let d:=selectBadMeter fee T S a b
  match d.value with
  | none=>⟨none,l.work+d.work+l.calls.length+2,l.calls++d.calls⟩
  | some bad=>let x:=subtreeLabelsMeter S bad.badArc;let z:=boundaryMeter T x.value bad.c
   ⟨z.value.map (.remaining bad),l.work+d.work+x.work+z.work+l.calls.length+4,l.calls++d.calls⟩
 | some s=>⟨some (.prefix s),l.work+2,l.calls⟩

theorem final_value (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) :
 (finalMeter fee T S a b).value=selectFinal T S a b := by
 simp only [finalMeter,selectFinal,local_value,select_bad_value,subtree_labels_value,boundary_value]
 generalize hl : selectLocal T S a b=o
 cases o with
 | none=>rfl
 | some s=>cases s with
  | large e=>rfl
  | two c=>rfl
  | outside c=>rfl
  | remaining=>
   cases hd : selectBad T S a b with
   | none=>rfl
   | some d=>
    change Option.map (.remaining d) (selectBoundary T (subtreeLabels S d.badArc) d.c)=
     (selectBoundary T (subtreeLabels S d.badArc) d.c).bind (fun z=>some (.remaining d z))
    cases hz : selectBoundary T (subtreeLabels S d.badArc) d.c <;> rfl

theorem geometry_budget_mono (k K n : Nat) (cap : k≤K) :
 minimalBudget k n≤minimalBudget K n ∧ paintBudget k n≤paintBudget K n ∧
 outsideCheckBudget k n≤outsideCheckBudget K n ∧ incidentBudget k n≤incidentBudget K n ∧
 boundaryBudget k n≤boundaryBudget K n := by
 have core:=Nat.mul_le_mul_right n (Nat.mul_le_mul_right n (Nat.mul_le_mul_left 64 (Nat.add_le_add_right cap 1)))
 have mi : minimalBudget k n≤minimalBudget K n := by
  unfold minimalBudget
  exact Nat.mul_le_mul_left (2*n) (by omega)
 have paint : paintBudget k n≤paintBudget K n := by unfold paintBudget;omega
 have outside : outsideCheckBudget k n≤outsideCheckBudget K n := by unfold outsideCheckBudget;omega
 have atom : incidentAtBudget k n≤incidentAtBudget K n := by unfold incidentAtBudget;omega
 have inc : incidentBudget k n≤incidentBudget K n := by
  have mul:=Nat.mul_le_mul_right (2*n) (Nat.add_le_add_right atom 2)
  unfold incidentBudget;omega
 refine ⟨mi,paint,outside,inc,?_⟩
 unfold boundaryBudget;omega

def finalBudget (nt ns K : Nat) :=localBudget nt ns K+badCandidatesBudget ns K+
 (4*ns*ns+2*ns+2)+boundaryBudget ns nt+7*ns+9

theorem final_work (fee : CheckRequest→Nat) (T S : Tree) (a b L K : Nat)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 (primitive : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r →fee r≤K) :
 (finalMeter fee T S a b).work≤finalBudget (leaves T).length (leaves S).length K := by
 have l:=local_work fee T S a b L K tlabs slabs primitive
 have lc:=local_call_count fee T S a b ((leaves T).length+(leaves S).length) L (by omega) (by omega) tlabs slabs
 have d:=select_bad_work fee T S a b L K tlabs slabs primitive
 simp only [finalMeter]
 split
 · dsimp only;unfold finalBudget;omega
 · split
   · dsimp only;unfold finalBudget;omega
   · rename_i bad hd
     have source:=Rule5FinalClassification.selectBad_sound (by rw [←select_bad_value fee];exact hd)
     have address:=cuts_address S a b (by rw [cuts_value];exact source.1)
     have x:=subtree_labels_work S bad.badArc
     have payload:=subtree_labels_payload S bad.badArc
     have z:=boundary_work T (subtreeLabelsMeter S bad.badArc).value bad.c
     have mono:=(geometry_budget_mono _ (leaves S).length (leaves T).length payload.1).2.2.2.2
     dsimp only
     unfold finalBudget
     omega
 · dsimp only;unfold finalBudget;omega

theorem final_calls (fee : CheckRequest→Nat) (T S : Tree) (a b N L : Nat)
 (tcap : (leaves T).length≤N) (scap : (leaves S).length≤N)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 {r : CheckRequest} (mem : r∈(finalMeter fee T S a b).calls) : CheckDomain N L r := by
 have loc:=local_calls fee T S a b N L tcap scap tlabs slabs (r:=r)
 have bad:=bad_candidates_calls fee T S a b N L tcap scap tlabs slabs (r:=r)
 simp only [finalMeter] at mem
 split at mem
 · exact loc mem
 · split at mem
   all_goals rcases List.mem_append.1 mem with h|h
   all_goals first | exact loc h | exact bad h
 · exact loc mem

theorem final_call_count (fee : CheckRequest→Nat) (T S : Tree) (a b N L : Nat)
 (tcap : (leaves T).length≤N) (scap : (leaves S).length≤N)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L) :
 (finalMeter fee T S a b).calls.length≤7*(leaves S).length+3+(2*(leaves S).length)*(2*(leaves S).length) := by
 have l:=local_call_count fee T S a b N L tcap scap tlabs slabs
 have d:=bad_candidates_call_count fee T S a b
 simp only [finalMeter]
 split <;> (try split) <;> simp only [List.length_append,selectBadMeter] <;> omega
end Universal233.Rule5PendantLocalWork
