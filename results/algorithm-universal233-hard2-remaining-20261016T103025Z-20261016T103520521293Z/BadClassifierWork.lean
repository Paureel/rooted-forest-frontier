import ClassifierAtoms
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork CherryBranching Rule5FinalClassification

/-- Exact primitive request domain for every source subtree-label payload,
including invalid addresses, empty blocks and repeated labels. -/
theorem subtree_restriction_domain (T S : Tree) (e : RMAF.Vertex) (N L : Nat)
 (tcap : (leaves T).length≤N) (scap : (leaves S).length≤N)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L) :
 CheckDomain N L (.restriction T S (subtreeLabelsMeter S e).value) := by
 have p:=subtree_labels_payload S e
 exact ⟨tcap,scap,by omega,tlabs,slabs,fun x hx=>slabs x (p.2 hx)⟩

def badAtMeter (fee : CheckRequest→Nat) (T S : Tree) (e f : RMAF.Vertex) : CheckReceipt (Option BadSelection) :=
 let ne:=eqAddressMeter e f
 if ne.value then ⟨none,ne.work+2,[]⟩ else
  let l:=subtreeLabelsMeter S e;let c:=checkMeter fee (.restriction T S l.value)
  if c.value then ⟨none,ne.work+l.work+c.work+3,c.calls⟩ else
   let s:=subtreeMeter S f
   ⟨match s.value with | some (.leaf x)=>some ⟨e,f,x⟩ | _=>none,
    ne.work+l.work+c.work+s.work+6,c.calls⟩

theorem bad_at_value (fee : CheckRequest→Nat) (T S : Tree) (e f : RMAF.Vertex) :
 (badAtMeter fee T S e f).value=badAt T S e f := by
 by_cases he : e=f
 · subst f;simp [badAtMeter,badAt,eq_address_value]
 · cases hc : restrictionAgrees T S (subtreeLabels S e) <;>
    simp [badAtMeter,badAt,eq_address_value,he,subtree_labels_value,checkMeter,checkValue,hc,subtree_value] <;> rfl

def badAtBudget (n K : Nat) :=4*n*n+6*n+K+10

theorem bad_at_work (fee : CheckRequest→Nat) (T S : Tree) (e f : RMAF.Vertex) (K : Nat)
 (ecap : e.length≤(leaves S).length) (fcap : f.length≤(leaves S).length)
 (primitive : fee (.restriction T S (subtreeLabelsMeter S e).value)≤K) :
 (badAtMeter fee T S e f).work≤badAtBudget (leaves S).length K := by
 have ne:=eq_address_work e f
 have l:=subtree_labels_work S e
 have s:=subtree_work S f
 simp only [badAtMeter]
 split
 · dsimp only;unfold badAtBudget;omega
 · try dsimp only
   split <;> dsimp only <;> simp only [checkMeter] <;> unfold badAtBudget <;> omega

theorem bad_at_call_count (fee : CheckRequest→Nat) (T S : Tree) (e f : RMAF.Vertex) :
 (badAtMeter fee T S e f).calls.length≤1 := by
 simp only [badAtMeter]
 split
 · simp
 · try dsimp only
   split <;> simp [checkMeter]

theorem bad_at_call (fee : CheckRequest→Nat) (T S : Tree) (e f : RMAF.Vertex)
 {r : CheckRequest} (mem : r∈(badAtMeter fee T S e f).calls) :
 r=.restriction T S (subtreeLabelsMeter S e).value := by
 simp only [badAtMeter] at mem
 split at mem
 · simp at mem
 · try dsimp only at mem
   split at mem <;> simpa [checkMeter] using mem

/-- The literal inner cut list is recomputed for each outer cut occurrence. -/
def badRowMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) (e : RMAF.Vertex) : CheckReceipt (List BadSelection) :=
 let c:=cutsMeter S a b;let r:=optionsMeter (badAtMeter fee T S e) c.value
 ⟨r.value,c.work+r.work+1,r.calls⟩

theorem bad_row_value (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) (e : RMAF.Vertex) :
 (badRowMeter fee T S a b e).value=(cuts S a b).filterMap (badAt T S e) := by
 simp only [badRowMeter,options_value,bad_at_value,cuts_value]

def badRowBudget (n K : Nat) :=cutsBudget n+(badAtBudget n K+4)*(2*n)+2

theorem bad_row_work (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) (e : RMAF.Vertex) (L K : Nat)
 (ecap : e.length≤(leaves S).length)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 (primitive : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r →fee r≤K) :
 (badRowMeter fee T S a b e).work≤badRowBudget (leaves S).length K := by
 have c:=cuts_work S a b
 have n:=cuts_count S a b
 have row:=options_work (badAtMeter fee T S e) (cutsMeter S a b).value (badAtBudget (leaves S).length K) 1 (by
  intro f hf
  have fc:=cuts_address S a b hf
  exact ⟨bad_at_work fee T S e f K ecap (by omega)
   (primitive _ (subtree_restriction_domain T S e _ L (by omega) (by omega) tlabs slabs)),bad_at_call_count fee T S e f⟩)
 have slots:=Nat.mul_le_mul_left (badAtBudget (leaves S).length K+4) n
 simp only [Nat.add_assoc] at row
 change (optionsMeter (badAtMeter fee T S e) (cutsMeter S a b).value).work≤
  (badAtBudget (leaves S).length K+4)*(cutsMeter S a b).value.length+1 at row
 simp only [badRowMeter,badRowBudget]
 omega

theorem bad_row_counts (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) (e : RMAF.Vertex) :
 (badRowMeter fee T S a b e).value.length≤2*(leaves S).length ∧
 (badRowMeter fee T S a b e).calls.length≤2*(leaves S).length := by
 have n:=cuts_count S a b
 have v:=options_count (badAtMeter fee T S e) (cutsMeter S a b).value
 have c:=options_calls_count (badAtMeter fee T S e) (cutsMeter S a b).value 1 (fun f _=>bad_at_call_count fee T S e f)
 simp only [badRowMeter]
 omega

/-- FlatMap receipt composition pays source-list append and request append. -/
def concatMeter {α β : Type} (f : α→CheckReceipt (List β)) : List α→CheckReceipt (List β)
 | []=>⟨[],1,[]⟩
 | x::xs=>let a:=f x;let r:=concatMeter f xs
           ⟨a.value++r.value,a.work+r.work+a.value.length+a.calls.length+2,a.calls++r.calls⟩

theorem concat_value {α β : Type} (f : α→CheckReceipt (List β)) (xs : List α) :
 (concatMeter f xs).value=xs.flatMap (fun x=>(f x).value) := by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>simp only [concatMeter,List.flatMap_cons,ih]

theorem concat_work {α β : Type} (f : α→CheckReceipt (List β)) (xs : List α) (B V C : Nat)
 (caps : ∀x,x∈xs →(f x).work≤B ∧ (f x).value.length≤V ∧ (f x).calls.length≤C) :
 (concatMeter f xs).work≤(B+V+C+2)*xs.length+1 := by
 induction xs with
 | nil=>simp [concatMeter]
 | cons x xs ih=>
  have a:=caps x (by simp)
  have tail:=ih (fun y hy=>caps y (by simp [hy]))
  simp only [concatMeter,List.length_cons,Nat.mul_succ]
  omega

theorem concat_calls_count {α β : Type} (f : α→CheckReceipt (List β)) (xs : List α) (C : Nat)
 (caps : ∀x,x∈xs →(f x).calls.length≤C) :
 (concatMeter f xs).calls.length≤C*xs.length := by
 induction xs with
 | nil=>simp [concatMeter]
 | cons x xs ih=>
  have a:=caps x (by simp)
  have tail:=ih (fun y hy=>caps y (by simp [hy]))
  simp only [concatMeter,List.length_append,List.length_cons,Nat.mul_succ]
  omega

theorem concat_call {α β : Type} (f : α→CheckReceipt (List β)) (xs : List α)
 {r : CheckRequest} (mem : r∈(concatMeter f xs).calls) : ∃x,x∈xs ∧ r∈(f x).calls := by
 induction xs with
 | nil=>simp [concatMeter] at mem
 | cons x xs ih=>
  simp only [concatMeter,List.mem_append] at mem
  rcases mem with h|h
  · exact ⟨x,by simp,h⟩
  · obtain ⟨y,hy,hr⟩:=ih h;exact ⟨y,by simp [hy],hr⟩

def badCandidatesMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt (List BadSelection) :=
 let c:=cutsMeter S a b;let r:=concatMeter (badRowMeter fee T S a b) c.value
 ⟨r.value,c.work+r.work+1,r.calls⟩

theorem bad_candidates_value (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) :
 (badCandidatesMeter fee T S a b).value=badCandidates T S a b := by
 simp only [badCandidatesMeter,concat_value,bad_row_value,cuts_value,badCandidates]

def badCandidatesBudget (n K : Nat) :=cutsBudget n+(badRowBudget n K+4*n+2)*(2*n)+2

theorem bad_candidates_work (fee : CheckRequest→Nat) (T S : Tree) (a b L K : Nat)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 (primitive : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r →fee r≤K) :
 (badCandidatesMeter fee T S a b).work≤badCandidatesBudget (leaves S).length K := by
 have c:=cuts_work S a b
 have n:=cuts_count S a b
 have rows:=concat_work (badRowMeter fee T S a b) (cutsMeter S a b).value
  (badRowBudget (leaves S).length K) (2*(leaves S).length) (2*(leaves S).length) (by
   intro e he
   have ec:=cuts_address S a b he
   exact ⟨bad_row_work fee T S a b e L K (by omega) tlabs slabs primitive,bad_row_counts fee T S a b e⟩)
 have slots:=Nat.mul_le_mul_left (badRowBudget (leaves S).length K+4*(leaves S).length+2) n
 have eq : badRowBudget (leaves S).length K+2*(leaves S).length+2*(leaves S).length+2=
  badRowBudget (leaves S).length K+4*(leaves S).length+2 := by omega
 rw [eq] at rows
 simp only [badCandidatesMeter,badCandidatesBudget]
 omega

theorem bad_candidates_calls (fee : CheckRequest→Nat) (T S : Tree) (a b N L : Nat)
 (tcap : (leaves T).length≤N) (scap : (leaves S).length≤N)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 {r : CheckRequest} (mem : r∈(badCandidatesMeter fee T S a b).calls) : CheckDomain N L r := by
 obtain ⟨e,he,hr⟩:=concat_call (badRowMeter fee T S a b) (cutsMeter S a b).value mem
 obtain ⟨f,hf,hcall⟩:=options_call (badAtMeter fee T S e) (cutsMeter S a b).value hr
 rw [bad_at_call fee T S e f hcall]
 exact subtree_restriction_domain T S e N L tcap scap tlabs slabs

theorem bad_candidates_call_count (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) :
 (badCandidatesMeter fee T S a b).calls.length≤(2*(leaves S).length)*(2*(leaves S).length) := by
 have c:=concat_calls_count (badRowMeter fee T S a b) (cutsMeter S a b).value (2*(leaves S).length)
  (fun e _=>(bad_row_counts fee T S a b e).2)
 have n:=cuts_count S a b
 have mul:=Nat.mul_le_mul_left (2*(leaves S).length) n
 exact Nat.le_trans c mul

def selectBadMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt (Option BadSelection) :=
 let c:=badCandidatesMeter fee T S a b;⟨c.value.head?,c.work+1,c.calls⟩

theorem select_bad_value (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) :
 (selectBadMeter fee T S a b).value=selectBad T S a b := by
 simp only [selectBadMeter,bad_candidates_value,selectBad]

theorem select_bad_work (fee : CheckRequest→Nat) (T S : Tree) (a b L K : Nat)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 (primitive : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r →fee r≤K) :
 (selectBadMeter fee T S a b).work≤badCandidatesBudget (leaves S).length K+1 := by
 have:=bad_candidates_work fee T S a b L K tlabs slabs primitive
 simp only [selectBadMeter]
 omega
end Universal233.Rule5PendantLocalWork
