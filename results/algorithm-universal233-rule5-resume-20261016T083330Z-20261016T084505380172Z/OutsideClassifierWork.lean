import PrefixClassifierWork
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork CherryBranching Rule5Classification

def coreCheckMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt Bool :=
 let c:=coreMeter S a b;let r:=checkMeter fee (.restriction T S c.value)
 ⟨r.value,c.work+r.work+1,r.calls⟩

def coreContainsMeter (S : Tree) (a b x : Nat) : Measured Bool :=
 let c:=coreMeter S a b;let r:=containsMeter x c.value
 ⟨r.value,c.work+r.work+1⟩

def outsideGuards (fee : CheckRequest→Nat) (T S : Tree) (a b p q : Nat) : List (Unit→CheckReceipt Bool) :=
 [fun _=>coreCheckMeter fee T S a b,
  fun _=>liftMeter (coreContainsMeter S a b p),fun _=>liftMeter (coreContainsMeter S a b q),
  fun _=>liftMeter ⟨p != a,1⟩,fun _=>liftMeter ⟨p != b,1⟩,
  fun _=>liftMeter ⟨q != a,1⟩,fun _=>liftMeter ⟨q != b,1⟩]

def outsideAtMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) (c : CherryRow) : CheckReceipt (Option OutsideSelection) :=
 let (j,p,q):=c;let r:=andSequence (outsideGuards fee T S a b p q)
 ⟨if r.value then some ⟨j,p,q⟩ else none,r.work+4,r.calls⟩

theorem outside_at_value (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) (c : CherryRow) :
 (outsideAtMeter fee T S a b c).value=outsideAt T S a b c := by
 rcases c with ⟨j,p,q⟩
 simp only [outsideAtMeter,outsideAt,and_sequence_value,outsideGuards,List.all_cons,List.all_nil,
  coreCheckMeter,checkMeter,checkValue,core_value,liftMeter,coreContainsMeter,contains_value,
  Bool.and_true,Bool.and_assoc]

def outsideGuardBudget (n K : Nat) :=coreBudget n+2*n+K+4
def outsideAtBudget (n K : Nat) :=(outsideGuardBudget n K+2)*7+5

theorem outside_guard_bounds (fee : CheckRequest→Nat) (T S : Tree) (a b p q L K : Nat)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 (primitive : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r →fee r≤K) :
 ∀f,f∈outsideGuards fee T S a b p q →
  (f ()).work≤outsideGuardBudget (leaves S).length K ∧ (f ()).calls.length≤1 := by
 have c:=core_work S a b
 have dom:=core_domain S a b
 have pc:=contains_work p (coreMeter S a b).value
 have qc:=contains_work q (coreMeter S a b).value
 have feeBound:=primitive (.restriction T S (coreMeter S a b).value)
  (show CheckDomain ((leaves T).length+(leaves S).length) L (.restriction T S (coreMeter S a b).value) from
    ⟨by omega,by omega,by omega,tlabs,slabs,fun x hx=>slabs x (dom.2 hx)⟩)
 intro f hf
 simp only [outsideGuards,List.mem_cons,List.not_mem_nil,or_false] at hf
 rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals simp only [coreCheckMeter,coreContainsMeter,liftMeter,checkMeter,List.length_singleton,List.length_nil]
 all_goals constructor <;> unfold outsideGuardBudget <;> omega

theorem outside_at_work (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) (c : CherryRow) (L K : Nat)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 (primitive : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r →fee r≤K) :
 (outsideAtMeter fee T S a b c).work≤outsideAtBudget (leaves S).length K := by
 rcases c with ⟨j,p,q⟩
 have seq:=and_sequence_work (outsideGuards fee T S a b p q) (outsideGuardBudget (leaves S).length K) 1
  (outside_guard_bounds fee T S a b p q L K tlabs slabs primitive)
 change (andSequence (outsideGuards fee T S a b p q)).work≤(outsideGuardBudget (leaves S).length K+2)*7+1 at seq
 simp only [outsideAtMeter,outsideAtBudget]
 omega

theorem outside_at_call_count (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) (c : CherryRow) :
 (outsideAtMeter fee T S a b c).calls.length≤1 := by
 rcases c with ⟨j,p,q⟩
 have seq:=and_sequence_call_count (outsideGuards fee T S a b p q)
 simpa only [outsideAtMeter,outsideGuards,coreCheckMeter,checkMeter,liftMeter,List.map_cons,List.map_nil,
  List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_zero] using seq

theorem outside_at_calls (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) (c : CherryRow) (N L : Nat)
 (tcap : (leaves T).length≤N) (scap : (leaves S).length≤N)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 {r : CheckRequest} (mem : r∈(outsideAtMeter fee T S a b c).calls) : CheckDomain N L r := by
 rcases c with ⟨j,p,q⟩
 obtain ⟨f,hf,hr⟩:=and_sequence_call (outsideGuards fee T S a b p q) mem
 simp only [outsideGuards,List.mem_cons,List.not_mem_nil,or_false] at hf
 rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals simp only [liftMeter,List.not_mem_nil] at hr
 have eq : r=.restriction T S (coreMeter S a b).value := by simpa only [coreCheckMeter,checkMeter,List.mem_singleton] using hr
 rw [eq]
 have dom:=core_domain S a b
 exact ⟨tcap,scap,by omega,tlabs,slabs,fun x hx=>slabs x (dom.2 hx)⟩

def selectOutsideMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt (Option OutsideSelection) :=
 optionsHeadMeter (cherriesMeter S) (outsideAtMeter fee T S a b)

theorem select_outside_value (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) :
 (selectOutsideMeter fee T S a b).value=selectOutside T S a b := by
 simp only [selectOutsideMeter,options_head_value,outside_at_value,cherries_value,selectOutside,outsideCandidates]

def selectOutsideBudget (n K : Nat) :=16*n*n+(outsideAtBudget n K+4)*n+3

theorem select_outside_work (fee : CheckRequest→Nat) (T S : Tree) (a b L K : Nat)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 (primitive : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r →fee r≤K) :
 (selectOutsideMeter fee T S a b).work≤selectOutsideBudget (leaves S).length K := by
 have c:=cherries_work S
 have n:=cherries_count S
 have seq:=options_head_work (cherriesMeter S) (outsideAtMeter fee T S a b) (outsideAtBudget (leaves S).length K) 1 (by
  intro row _
  exact ⟨outside_at_work fee T S a b row L K tlabs slabs primitive,outside_at_call_count fee T S a b row⟩)
 change (selectOutsideMeter fee T S a b).work≤(cherriesMeter S).work+
  (outsideAtBudget (leaves S).length K+4)*(cherriesMeter S).value.length+3 at seq
 have slots:=Nat.mul_le_mul_left (outsideAtBudget (leaves S).length K+4) n
 rw [←cherries_value] at slots
 unfold selectOutsideBudget
 omega

theorem select_outside_call_count (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) :
 (selectOutsideMeter fee T S a b).calls.length≤(leaves S).length := by
 have c:=options_calls_count (outsideAtMeter fee T S a b) (cherriesMeter S).value 1
  (fun row _=>outside_at_call_count fee T S a b row)
 have n:=cherries_count S
 rw [←cherries_value] at n
 simpa only [selectOutsideMeter,optionsHeadMeter,Nat.one_mul] using Nat.le_trans c (by simpa using n)

theorem select_outside_calls (fee : CheckRequest→Nat) (T S : Tree) (a b N L : Nat)
 (tcap : (leaves T).length≤N) (scap : (leaves S).length≤N)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 {r : CheckRequest} (mem : r∈(selectOutsideMeter fee T S a b).calls) : CheckDomain N L r := by
 obtain ⟨row,hrow,hr⟩:=options_call (outsideAtMeter fee T S a b) (cherriesMeter S).value mem
 exact outside_at_calls fee T S a b row N L tcap scap tlabs slabs hr
end Universal233.Rule5PendantLocalWork
