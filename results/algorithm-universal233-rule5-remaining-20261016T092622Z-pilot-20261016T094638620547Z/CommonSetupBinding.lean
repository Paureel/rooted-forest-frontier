import SetupPolynomial
import CommonConsumer
namespace Universal233.Rule5RemainingLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5PendantLocalWork
open Rule5Local Rule5Classification Rule5FinalClassification Rule5CommonSelector
open OrdinaryCommonSplit OrdinaryCommonSplit.Source OrdinaryCommonSplit.Caller

def commonSetupMeter (T S : Tree) (a b : Nat) (d : BadSelection) : Measured (Option Setup) :=
 let x:=subtreeLabelsMeter S d.badArc;let c:=coreMeter S a b
 let y:=c.value++[d.c];let r:=setupMeter T S x.value y d.badArc
 ⟨r.value,x.work+c.work+c.value.length+r.work+3⟩

theorem common_setup_value (T S : Tree) (a b : Nat) (d : BadSelection) :
 (commonSetupMeter T S a b d).value=
 buildSetup T S (subtreeLabels S d.badArc) (outsideLabels S a b d) d.badArc := by
 simp only [commonSetupMeter,setup_value,subtree_labels_value,core_value,outsideLabels]

def commonSetupBudget (nt ns x : Nat) :=4*ns*ns+2*ns+2+coreBudget ns+ns+
 setupBudget (nt+ns+2) x nt+3

theorem common_setup_work (fee : CheckRequest→Nat) {T S : Tree} {i q : RMAF.Vertex}
 {a b : Nat} {d : BadSelection} (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (sel : (finalMeter fee T S a b).value=some (.remaining d (.one q))) :
 (commonSetupMeter T S a b d).work≤commonSetupBudget (leaves T).length (leaves S).length (subtreeLabels S d.badArc).length := by
 have sel' : selectFinal T S a b=some (.remaining d (.one q)):=by rw [←final_value fee];exact sel
 have prop:=properPair_parts (admitted_parts ad).1
 obtain ⟨_,_,_,_,pt,_,_⟩:=selected_common_checks ch ad sel'
 have perm:=FinalCutRecovery.checked_flatten_perm T [subtreeLabels S d.badArc,outsideLabels S a b d] prop.1 pt
 have len:=perm.length_eq
 have payload:=final_payload fee T S a b sel
 have arc : d.badArc.length+1≤(leaves S).length:=payload.1
 have x:=subtree_labels_work S d.badArc
 have c:=core_work S a b;have cd:=core_domain S a b
 have setup:=setup_work T S (subtreeLabels S d.badArc) (outsideLabels S a b d) d.badArc
  ((leaves T).length+(leaves S).length+2) (by omega) (by omega) (by simpa using Nat.le_add_right (leaves T).length ((leaves S).length+2)) (by omega) (by omega)
 simp only [commonSetupMeter,subtree_labels_value,core_value,outsideLabels] at setup ⊢
 unfold commonSetupBudget
 simp only [List.flatten_cons,List.flatten_nil,List.length_append,List.length_nil,Nat.add_zero] at len
 have identity : (subtreeLabels S d.badArc).length+(coreLabels S a b++[d.c]).length=(leaves T).length := by simpa only [outsideLabels] using len
 omega
end Universal233.Rule5RemainingLocalWork
