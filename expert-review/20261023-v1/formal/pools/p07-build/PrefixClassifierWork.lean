import BoundaryClassifierWork
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork CherryBranching Rule5Classification

def largeAtMeter (fee : CheckRequest→Nat) (T S : Tree) (e : RMAF.Vertex) : CheckReceipt (Option RMAF.Vertex) :=
 let l:=subtreeLabelsMeter S e;let c:=checkMeter fee (.restriction T S l.value)
 if c.value then let m:=subtreeLabelsMeter S e
  ⟨if 3≤m.value.length then some e else none,l.work+c.work+m.work+m.value.length+4,c.calls⟩
 else ⟨none,l.work+c.work+2,c.calls⟩

theorem large_at_value (fee : CheckRequest→Nat) (T S : Tree) (e : RMAF.Vertex) :
 (largeAtMeter fee T S e).value=
  (if restrictionAgrees T S (subtreeLabels S e) && decide (3≤(subtreeLabels S e).length) then some e else none) := by
 simp only [largeAtMeter,checkMeter,checkValue,subtree_labels_value]
 split <;> simp_all

def largeAtBudget (n K : Nat) :=2*(4*n*n+2*n+2)+n+K+5

theorem large_at_work (fee : CheckRequest→Nat) (T S : Tree) (e : RMAF.Vertex) (K : Nat)
 (ecap : e.length≤(leaves S).length)
 (primitive : fee (.restriction T S (subtreeLabelsMeter S e).value)≤K) :
 (largeAtMeter fee T S e).work≤largeAtBudget (leaves S).length K := by
 have l:=subtree_labels_work S e
 have dom:=subtree_labels_payload S e
 simp only [largeAtMeter]
 split <;> dsimp only <;> simp only [checkMeter] <;> unfold largeAtBudget <;> omega

theorem large_at_calls (fee : CheckRequest→Nat) (T S : Tree) (e : RMAF.Vertex) :
 (largeAtMeter fee T S e).calls=[.restriction T S (subtreeLabelsMeter S e).value] := by
 simp only [largeAtMeter]
 split <;> rfl

theorem filter_map_keep {α : Type} (p : α→Bool) (xs : List α) :
 (xs.filterMap (fun x=>if p x then some x else none))=xs.filter p := by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>cases hp : p x <;> simp [hp,ih]

/-- Shared source spine for literal filterMap then head; this evaluates all
candidates before head selection, including later failures and duplicates. -/
def optionsHeadMeter {α β : Type} (cs : Measured (List α)) (f : α→CheckReceipt (Option β)) : CheckReceipt (Option β) :=
 let r:=optionsMeter f cs.value;⟨r.value.head?,cs.work+r.work+2,r.calls⟩

theorem options_head_value {α β : Type} (cs : Measured (List α)) (f : α→CheckReceipt (Option β)) :
 (optionsHeadMeter cs f).value=(cs.value.filterMap (fun x=>(f x).value)).head? := by
 simp only [optionsHeadMeter,options_value]

theorem options_head_work {α β : Type} (cs : Measured (List α)) (f : α→CheckReceipt (Option β)) (B C : Nat)
 (caps : ∀x,x∈cs.value →(f x).work≤B ∧ (f x).calls.length≤C) :
 (optionsHeadMeter cs f).work≤cs.work+(B+C+3)*cs.value.length+3 := by
 have:=options_work f cs.value B C caps
 simp only [optionsHeadMeter]
 omega

def selectLargeMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt (Option RMAF.Vertex) :=
 optionsHeadMeter (cutsMeter S a b) (largeAtMeter fee T S)

theorem select_large_value (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) :
 (selectLargeMeter fee T S a b).value=selectLarge T S a b := by
 simp only [selectLargeMeter,options_head_value,large_at_value,cuts_value,filter_map_keep,selectLarge,largeCandidates]

def selectLargeBudget (n K : Nat) :=cutsBudget n+(largeAtBudget n K+4)*(2*n)+3

theorem select_large_work (fee : CheckRequest→Nat) (T S : Tree) (a b L K : Nat)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 (primitive : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r →fee r≤K) :
 (selectLargeMeter fee T S a b).work≤selectLargeBudget (leaves S).length K := by
 have c:=cuts_work S a b
 have n:=cuts_count S a b
 have seq:=options_head_work (cutsMeter S a b) (largeAtMeter fee T S) (largeAtBudget (leaves S).length K) 1 (by
  intro e he
  have cap:=cuts_address S a b he
  exact ⟨large_at_work fee T S e K (by omega)
   (primitive _ (subtree_restriction_domain T S e _ L (by omega) (by omega) tlabs slabs)),by rw [large_at_calls];simp⟩)
 change (selectLargeMeter fee T S a b).work≤(cutsMeter S a b).work+
  (largeAtBudget (leaves S).length K+4)*(cutsMeter S a b).value.length+3 at seq
 have slots:=Nat.mul_le_mul_left (largeAtBudget (leaves S).length K+4) n
 unfold selectLargeBudget
 omega

def sizeTwoAtMeter (fee : CheckRequest→Nat) (T S : Tree) (e : RMAF.Vertex) : CheckReceipt (Option SizeTwoSelection) :=
 let l:=subtreeLabelsMeter S e;let c:=checkMeter fee (.restriction T S l.value)
 if c.value then let t:=subtreeMeter S e
  ⟨match t.value with | some (.node (.leaf p) (.leaf q))=>some ⟨e,p,q⟩ | _=>none,l.work+c.work+t.work+5,c.calls⟩
 else ⟨none,l.work+c.work+2,c.calls⟩

theorem size_two_at_value (fee : CheckRequest→Nat) (T S : Tree) (e : RMAF.Vertex) :
 (sizeTwoAtMeter fee T S e).value=sizeTwoAt T S e := by
 simp only [sizeTwoAtMeter,sizeTwoAt,checkMeter,checkValue,subtree_labels_value,subtree_value]
 split <;> simp_all <;> rfl

def sizeTwoAtBudget (n K : Nat) :=4*n*n+4*n+K+8

theorem size_two_at_work (fee : CheckRequest→Nat) (T S : Tree) (e : RMAF.Vertex) (K : Nat)
 (ecap : e.length≤(leaves S).length)
 (primitive : fee (.restriction T S (subtreeLabelsMeter S e).value)≤K) :
 (sizeTwoAtMeter fee T S e).work≤sizeTwoAtBudget (leaves S).length K := by
 have l:=subtree_labels_work S e
 have s:=subtree_work S e
 simp only [sizeTwoAtMeter]
 split <;> dsimp only <;> simp only [checkMeter] <;> unfold sizeTwoAtBudget <;> omega

theorem size_two_at_calls (fee : CheckRequest→Nat) (T S : Tree) (e : RMAF.Vertex) :
 (sizeTwoAtMeter fee T S e).calls=[.restriction T S (subtreeLabelsMeter S e).value] := by
 simp only [sizeTwoAtMeter]
 split <;> rfl

def selectSizeTwoMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt (Option SizeTwoSelection) :=
 optionsHeadMeter (cutsMeter S a b) (sizeTwoAtMeter fee T S)

theorem select_size_two_value (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) :
 (selectSizeTwoMeter fee T S a b).value=selectSizeTwo T S a b := by
 simp only [selectSizeTwoMeter,options_head_value,size_two_at_value,cuts_value,selectSizeTwo,sizeTwoCandidates]

def selectSizeTwoBudget (n K : Nat) :=cutsBudget n+(sizeTwoAtBudget n K+4)*(2*n)+3

theorem select_size_two_work (fee : CheckRequest→Nat) (T S : Tree) (a b L K : Nat)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 (primitive : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r →fee r≤K) :
 (selectSizeTwoMeter fee T S a b).work≤selectSizeTwoBudget (leaves S).length K := by
 have c:=cuts_work S a b
 have n:=cuts_count S a b
 have seq:=options_head_work (cutsMeter S a b) (sizeTwoAtMeter fee T S) (sizeTwoAtBudget (leaves S).length K) 1 (by
  intro e he
  have cap:=cuts_address S a b he
  exact ⟨size_two_at_work fee T S e K (by omega)
   (primitive _ (subtree_restriction_domain T S e _ L (by omega) (by omega) tlabs slabs)),by rw [size_two_at_calls];simp⟩)
 change (selectSizeTwoMeter fee T S a b).work≤(cutsMeter S a b).work+
  (sizeTwoAtBudget (leaves S).length K+4)*(cutsMeter S a b).value.length+3 at seq
 have slots:=Nat.mul_le_mul_left (sizeTwoAtBudget (leaves S).length K+4) n
 unfold selectSizeTwoBudget
 omega

/-- Both literal scans invoke exactly one restriction primitive per source cut. -/
theorem prefix_selector_calls (fee : CheckRequest→Nat) (T S : Tree) (a b N L : Nat)
 (tcap : (leaves T).length≤N) (scap : (leaves S).length≤N)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L) :
 (selectLargeMeter fee T S a b).calls.length≤2*(leaves S).length ∧
 (selectSizeTwoMeter fee T S a b).calls.length≤2*(leaves S).length ∧
 (∀r,r∈(selectLargeMeter fee T S a b).calls →CheckDomain N L r) ∧
 (∀r,r∈(selectSizeTwoMeter fee T S a b).calls →CheckDomain N L r) := by
 have c:=cuts_count S a b
 have l:=options_calls_count (largeAtMeter fee T S) (cutsMeter S a b).value 1 (by intro e _;rw [large_at_calls];simp)
 have s:=options_calls_count (sizeTwoAtMeter fee T S) (cutsMeter S a b).value 1 (by intro e _;rw [size_two_at_calls];simp)
 refine ⟨by simpa only [selectLargeMeter,optionsHeadMeter,Nat.one_mul] using Nat.le_trans l (by simpa using c),
  by simpa only [selectSizeTwoMeter,optionsHeadMeter,Nat.one_mul] using Nat.le_trans s (by simpa using c),?_,?_⟩
 · intro r hr
   obtain ⟨e,he,hm⟩:=options_call (largeAtMeter fee T S) (cutsMeter S a b).value hr
   rw [large_at_calls] at hm
   have eq : r=.restriction T S (subtreeLabelsMeter S e).value := by simpa using hm
   rw [eq];exact subtree_restriction_domain T S e N L tcap scap tlabs slabs
 · intro r hr
   obtain ⟨e,he,hm⟩:=options_call (sizeTwoAtMeter fee T S) (cutsMeter S a b).value hr
   rw [size_two_at_calls] at hm
   have eq : r=.restriction T S (subtreeLabelsMeter S e).value := by simpa using hm
   rw [eq];exact subtree_restriction_domain T S e N L tcap scap tlabs slabs
end Universal233.Rule5PendantLocalWork
