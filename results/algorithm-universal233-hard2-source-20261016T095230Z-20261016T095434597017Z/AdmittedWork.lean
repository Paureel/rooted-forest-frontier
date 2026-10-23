import AdmittedCheckCalls
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork CherryBranching

def notMeter (m : Measured Bool) : Measured Bool :=⟨!m.value,m.work+1⟩
def cutLengthMeter (S : Tree) (a b : Nat) : Measured Bool :=
 let e:=cutsMeter S a b;⟨e.value.length==2,e.work+e.value.length+2⟩
def filteredLengthMeter (fee : CheckRequest→Nat) (T S : Tree) (P : List (List Nat)) : CheckReceipt Bool :=
 let r:=restrictionFilterMeter fee T S P
 ⟨r.value.length==2,r.work+r.value.length+2,r.calls⟩

def admittedGuards (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) (P : List (List Nat)) : List (Unit→CheckReceipt Bool) :=
 [fun _=>liftMeter (properPairMeter T S),
  fun _=>liftMeter (hasCherryMeter T a b),
  fun _=>liftMeter (earlierMeter T S),fun _=>liftMeter (earlierMeter S T),
  fun _=>liftMeter (notMeter (admittedRule4Meter T S)),
  fun _=>liftMeter (notMeter (admittedRule4Meter S T)),
  fun _=>liftMeter (cutLengthMeter S a b),
  fun _=>checkMeter fee (.embedding T P),fun _=>checkMeter fee (.embedding S P),
  fun _=>filteredLengthMeter fee T S P]

def admittedMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt Bool :=
 let p:=partitionMeter S a b
 let r:=andSequence (admittedGuards fee T S a b p.value)
 ⟨r.value,p.work+r.work+1,r.calls⟩

theorem admitted_value (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) :
 (admittedMeter fee T S a b).value=Rule5Local.admitted T S a b := by
 simp only [admittedMeter,and_sequence_value,admittedGuards,List.all_cons,List.all_nil,
   liftMeter,proper_pair_value,has_cherry_value,earlier_value,notMeter,admitted_rule4_value,
   cutLengthMeter,cuts_value,checkMeter,checkValue,filteredLengthMeter,restriction_filter_value,
   partition_value,Rule5Local.admitted,Bool.and_true,Bool.and_assoc]

def admittedGuardBudget (nt ns K : Nat) : Nat :=
 properPolynomial (nt+ns)+(16*nt*nt+8*nt+2)+earlierBudget nt ns+earlierBudget ns nt+
 admittedRule4Budget nt ns+admittedRule4Budget ns nt+cutsBudget ns+2*ns+K+
 (K+3)*(2*ns+1)+2*ns+20

theorem admitted_guard_bounds (fee : CheckRequest→Nat) (T S : Tree) (a b L K : Nat)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 (primitive : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r →fee r≤K) :
 ∀f,f∈admittedGuards fee T S a b (partitionMeter S a b).value →
 (f ()).work≤admittedGuardBudget (leaves T).length (leaves S).length K ∧
 (f ()).calls.length≤2*(leaves S).length+3 := by
 have p:=proper_pair_work T S ((leaves T).length+(leaves S).length) (by omega) (by omega)
 have h:=has_cherry_work T a b
 have ef:=earlier_work T S
 have er:=earlier_work S T
 have rf:=admitted_rule4_work T S
 have rr:=admitted_rule4_work S T
 have cut:=cuts_work S a b
 have cutlen:=cuts_count S a b
 have dom:=partition_domain S a b
 have embf:=primitive (.embedding T (partitionMeter S a b).value)
   (partition_embedding_domain T S a b _ L (by omega) (by omega) tlabs slabs)
 have embr:=primitive (.embedding S (partitionMeter S a b).value)
   (partition_embedding_domain S S a b _ L (by omega) (by omega) slabs slabs)
 have filter:=restriction_filter_work fee T S (partitionMeter S a b).value K (by
   intro B hB
   exact primitive _ (partition_restriction_domain T S a b _ L (by omega) (by omega) tlabs slabs hB))
 have filterlen : (restrictionFilterMeter fee T S (partitionMeter S a b).value).value.length≤(partitionMeter S a b).value.length := by
   rw [restriction_filter_value];exact List.length_filter_le _ _
 have slots:=Nat.mul_le_mul_left (K+3) dom.1
 intro f mem
 simp only [admittedGuards,List.mem_cons,List.not_mem_nil,or_false] at mem
 rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals simp only [liftMeter,notMeter,cutLengthMeter,checkMeter,filteredLengthMeter,
   restriction_filter_calls,List.length_map,List.length_cons,List.length_nil]
 all_goals constructor <;> (try unfold admittedGuardBudget) <;> omega

def admittedBudget (nt ns K : Nat) :=partitionBudget ns+(admittedGuardBudget nt ns K+2*ns+4)*10+2

theorem admitted_work (fee : CheckRequest→Nat) (T S : Tree) (a b L K : Nat)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 (primitive : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r →fee r≤K) :
 (admittedMeter fee T S a b).work≤admittedBudget (leaves T).length (leaves S).length K := by
 have p:=partition_work S a b
 have seq:=and_sequence_work (admittedGuards fee T S a b (partitionMeter S a b).value)
   (admittedGuardBudget (leaves T).length (leaves S).length K) (2*(leaves S).length+3)
   (admitted_guard_bounds fee T S a b L K tlabs slabs primitive)
 have len : (admittedGuards fee T S a b (partitionMeter S a b).value).length=10 := by rfl
 rw [len] at seq
 simp only [admittedMeter,admittedBudget]
 omega

theorem admitted_check_domain (fee : CheckRequest→Nat) (T S : Tree) (a b N L : Nat)
 (tcap : (leaves T).length≤N) (scap : (leaves S).length≤N)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 {r : CheckRequest} (mem : r∈(admittedMeter fee T S a b).calls) : CheckDomain N L r := by
 obtain ⟨f,hf,hr⟩:=and_sequence_call (admittedGuards fee T S a b (partitionMeter S a b).value) mem
 simp only [admittedGuards,List.mem_cons,List.not_mem_nil,or_false] at hf
 rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals simp only [liftMeter,List.not_mem_nil] at hr
 · have eq : r=.embedding T (partitionMeter S a b).value := by simpa only [checkMeter,List.mem_singleton] using hr
   subst r
   exact partition_embedding_domain T S a b N L tcap scap tlabs slabs
 · have eq : r=.embedding S (partitionMeter S a b).value := by simpa only [checkMeter,List.mem_singleton] using hr
   subst r
   exact partition_embedding_domain S S a b N L scap scap slabs slabs
 · simp only [filteredLengthMeter,restriction_filter_calls] at hr
   obtain ⟨B,hB,rfl⟩:=List.mem_map.1 hr
   exact partition_restriction_domain T S a b N L tcap scap tlabs slabs hB
end Universal233.Rule5PendantLocalWork
