import SelectedChildrenWork
namespace Universal233.Rule5SelectedLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5PendantLocalWork
open CherryBranching CoreWork Rule5Classification Rule5FinalClassification Rule5OrdinaryDispatch

abbrev Forest := List (List Nat)
abbrev Ordinary := Tree→Tree→Nat→Option Forest
structure ForestQuery where
 child : Child
 budget : Nat
 deriving Repr,DecidableEq
structure ForestReceipt (α : Type) where
 value : α
 localWork : Nat
 recursiveWork : Nat
 calls : List ForestQuery
 deriving Repr

/-- Explicit recursive boundary at the literal GenericForest.solve call.
No statement here treats the forest solver's internal source work as free. -/
def childExecutionMeter (actual : Ordinary) (fee : ForestQuery→Nat) (T : Tree) (q : Nat) (c : Child) : ForestReceipt (Option Forest) :=
 if c.paid≤q then
  let r:=q-c.paid;let call:ForestQuery:=⟨c,r⟩
  ⟨GenericForest.solve actual (some T) c.sourceForest r,4,fee call,[call]⟩
 else ⟨none,2,0,[]⟩

theorem child_execution_value (actual : Ordinary) (fee : ForestQuery→Nat) (T : Tree) (q : Nat) (c : Child) :
 (childExecutionMeter actual fee T q c).value=childCall (OrdinaryDispatch.forestChild actual T) q c := by
 simp only [childExecutionMeter,childCall,remaining,OrdinaryDispatch.forestChild]
 split <;> rfl

def childrenAnswersMeter (actual : Ordinary) (fee : ForestQuery→Nat) (T : Tree) (q : Nat) : List Child→ForestReceipt (List Forest)
 | []=>⟨[],1,0,[]⟩
 | c::cs=>let a:=childExecutionMeter actual fee T q c;let r:=childrenAnswersMeter actual fee T q cs
  ⟨match a.value with | none=>r.value | some F=>F::r.value,
   a.localWork+r.localWork+a.calls.length+3,a.recursiveWork+r.recursiveWork,a.calls++r.calls⟩

theorem children_answers_value (actual : Ordinary) (fee : ForestQuery→Nat) (T : Tree) (q : Nat) (cs : List Child) :
 (childrenAnswersMeter actual fee T q cs).value=childAnswers actual T q cs := by
 induction cs with
 | nil=>rfl
 | cons c cs ih=>
  simp only [childrenAnswersMeter,childAnswers,List.filterMap_cons,child_execution_value] at *
  split <;> simp_all

theorem children_answers_count (actual : Ordinary) (fee : ForestQuery→Nat) (T : Tree) (q : Nat) (cs : List Child) :
 (childrenAnswersMeter actual fee T q cs).value.length≤cs.length := by
 rw [children_answers_value]
 exact List.length_filterMap_le _ _

theorem child_execution_local (actual : Ordinary) (fee : ForestQuery→Nat) (T : Tree) (q : Nat) (c : Child) :
 (childExecutionMeter actual fee T q c).localWork≤4 ∧ (childExecutionMeter actual fee T q c).calls.length≤1 := by
 simp only [childExecutionMeter]
 split <;> simp

theorem children_answers_local (actual : Ordinary) (fee : ForestQuery→Nat) (T : Tree) (q : Nat) (cs : List Child) :
 (childrenAnswersMeter actual fee T q cs).localWork≤8*cs.length+1 ∧
 (childrenAnswersMeter actual fee T q cs).calls.length≤cs.length := by
 induction cs with
 | nil=>simp [childrenAnswersMeter]
 | cons c cs ih=>
  have head:=child_execution_local actual fee T q c
  simp only [childrenAnswersMeter,List.length_cons,List.length_append]
  constructor <;> omega

theorem child_execution_recursive (actual : Ordinary) (fee : ForestQuery→Nat) (T : Tree) (q : Nat) (c : Child) :
 (childExecutionMeter actual fee T q c).recursiveWork=((childExecutionMeter actual fee T q c).calls.map fee).sum := by
 simp only [childExecutionMeter]
 split <;> simp

theorem children_answers_recursive (actual : Ordinary) (fee : ForestQuery→Nat) (T : Tree) (q : Nat) (cs : List Child) :
 (childrenAnswersMeter actual fee T q cs).recursiveWork=((childrenAnswersMeter actual fee T q cs).calls.map fee).sum := by
 induction cs with
 | nil=>rfl
 | cons c cs ih=>simp only [childrenAnswersMeter,List.map_append,List.sum_append,child_execution_recursive,ih]

theorem child_execution_call (actual : Ordinary) (fee : ForestQuery→Nat) (T : Tree) (q : Nat) (c : Child)
 {j : ForestQuery} (mem : j∈(childExecutionMeter actual fee T q c).calls) :
 j.child=c ∧ c.paid≤q ∧ j.budget=q-c.paid := by
 simp only [childExecutionMeter] at mem
 split at mem
 · rename_i h
   have eq : j=⟨c,q-c.paid⟩ := by simpa using mem
   subst j
   exact ⟨rfl,h,rfl⟩
 · simp at mem

theorem children_answers_call (actual : Ordinary) (fee : ForestQuery→Nat) (T : Tree) (q : Nat) (cs : List Child)
 {j : ForestQuery} (mem : j∈(childrenAnswersMeter actual fee T q cs).calls) :
 j.child∈cs ∧ j.child.paid≤q ∧ j.budget=q-j.child.paid := by
 induction cs with
 | nil=>simp [childrenAnswersMeter] at mem
 | cons c cs ih=>
  simp only [childrenAnswersMeter,List.mem_append] at mem
  rcases mem with h|h
  · have p:=child_execution_call actual fee T q c h
    rw [p.1]
    exact ⟨by simp,p.2⟩
  · have p:=ih h
    exact ⟨by simp [p.1],p.2⟩

/-- Unconditional checks inside the actual forest solver bound every returned
candidate, including a candidate which later fails original T/S agreement. -/
theorem children_answer_payload (actual : Ordinary) (T : Tree) (q : Nat) (cs : List Child) {F : Forest}
 (mem : F∈childAnswers actual T q cs) (nt : (leaves T).Nodup) :
 F.flatten.length=(leaves T).length ∧ F.length≤(leaves T).length ∧ F.flatten⊆leaves T := by
 obtain ⟨c,hc,answer⟩:=List.mem_filterMap.1 mem
 unfold childCall at answer
 obtain ⟨r,hr,hF⟩:=Option.bind_eq_some_iff.1 answer
 have sound:=GenericForest.solve_sound actual (some T) c.sourceForest r F hF
 have part : partitionCheck (leaves T) F=true := by
  simp only [ForestState.agrees,ForestState.labels,Bool.and_eq_true] at sound
  exact sound.1.1.1.1.2
 exact ⟨(FinalCutRecovery.checked_flatten_perm T F nt part).length_eq,
  SourceCoverage.partitionCheck_block_bound _ _ part,SourceCoverage.partitionCheck_subset _ _ part⟩

def acceptedMeter (agreementFee : Forest→Nat) (T S : Tree) (q : Nat) (F : Forest) : Measured Bool :=
 ⟨agreement T S F && decide (F.length-1≤q),agreementFee F+F.length+3⟩

/-- Uses the actual List.length score. The earlier common-merge meter uses
length-1, which has different ties on an empty candidate and is not reused. -/
def bestLengthMeter (check : Forest→Measured Bool) : List Forest→Measured (Option Forest)
 | []=>⟨none,1⟩
 | F::fs=>let c:=check F;let r:=bestLengthMeter check fs
  ⟨if c.value then match r.value with | none=>some F | some G=>if F.length≤G.length then some F else some G else r.value,
   c.work+r.work+F.length+(r.value.map List.length).getD 0+4⟩

theorem best_length_value (check : Forest→Measured Bool) (fs : List Forest) :
 (bestLengthMeter check fs).value=best List.length (fun F=>(check F).value) fs := by
 induction fs with
 | nil=>rfl
 | cons F fs ih=>
  simp only [bestLengthMeter,best,ih]
  cases hc : (check F).value <;> cases hr : best List.length (fun F=>(check F).value) fs <;> rfl

theorem best_length_work (check : Forest→Measured Bool) (fs : List Forest) (K N : Nat)
 (checks : ∀F,F∈fs →(check F).work≤K) (sizes : ∀F,F∈fs →F.length≤N) :
 (bestLengthMeter check fs).work≤(K+2*N+4)*fs.length+1 := by
 induction fs with
 | nil=>simp [bestLengthMeter]
 | cons F fs ih=>
  have tail:=ih (fun G hG=>checks G (by simp [hG])) (fun G hG=>sizes G (by simp [hG]))
  have c:=checks F (by simp)
  have f:=sizes F (by simp)
  have kept : ((bestLengthMeter check fs).value.map List.length).getD 0≤N := by
   cases h : (bestLengthMeter check fs).value with
   | none=>simp
   | some G=>
    have value : best List.length (fun F=>(check F).value) fs=some G := by rw [←best_length_value];exact h
    have mem:=(best_spec _ _ fs G value).1
    simpa using sizes G (by simp [mem])
  change (check F).work+(bestLengthMeter check fs).work+F.length+((bestLengthMeter check fs).value.map List.length).getD 0+4≤(K+2*N+4)*(fs.length+1)+1
  rw [Nat.mul_succ (K+2*N+4) fs.length]
  omega

structure ChildrenReceipt where
 value : Option Forest
 localWork : Nat
 recursiveWork : Nat
 calls : List ForestQuery
 agreementChecks : List Forest
 deriving Repr

def runChildrenMeter (actual : Ordinary) (forestFee : ForestQuery→Nat) (agreementFee : Forest→Nat) (T S : Tree) (q : Nat) (cs : List Child) : ChildrenReceipt :=
 let r:=childrenAnswersMeter actual forestFee T q cs
 let b:=bestLengthMeter (acceptedMeter agreementFee T S q) r.value
 ⟨b.value,r.localWork+b.work+r.value.length+2,r.recursiveWork,r.calls,r.value⟩

theorem run_children_value (actual : Ordinary) (forestFee : ForestQuery→Nat) (agreementFee : Forest→Nat) (T S : Tree) (q : Nat) (cs : List Child) :
 (runChildrenMeter actual forestFee agreementFee T S q cs).value=runChildren actual T S q cs := by
 simp only [runChildrenMeter,best_length_value,children_answers_value,acceptedMeter,runChildren,Rule5OrdinaryDispatch.accepted]
 rfl

theorem run_children_local (actual : Ordinary) (forestFee : ForestQuery→Nat) (agreementFee : Forest→Nat) (T S : Tree) (q : Nat) (cs : List Child) (K : Nat)
 (nt : (leaves T).Nodup)
 (checker : ∀F,F.flatten.length≤(leaves T).length →F.length≤(leaves T).length →F.flatten⊆leaves T →agreementFee F≤K) :
 (runChildrenMeter actual forestFee agreementFee T S q cs).localWork≤(K+3*(leaves T).length+16)*cs.length+4 := by
 have caller:=children_answers_local actual forestFee T q cs
 have count:=children_answers_count actual forestFee T q cs
 have bounds : ∀F,F∈(childrenAnswersMeter actual forestFee T q cs).value →
  F.flatten.length=(leaves T).length ∧ F.length≤(leaves T).length ∧ F.flatten⊆leaves T := by
  intro F hF;rw [children_answers_value] at hF;exact children_answer_payload actual T q cs hF nt
 have best:=best_length_work (acceptedMeter agreementFee T S q) (childrenAnswersMeter actual forestFee T q cs).value
  (K+(leaves T).length+3) (leaves T).length (by
   intro F hF;have p:=bounds F hF;have c:=checker F (by omega) p.2.1 p.2.2
   simp only [acceptedMeter];omega) (fun F hF=>(bounds F hF).2.1)
 have coef : K+(leaves T).length+3+2*(leaves T).length+4=K+3*(leaves T).length+7 := by omega
 rw [coef] at best
 have slots:=Nat.mul_le_mul_left (K+3*(leaves T).length+7) count
 simp only [runChildrenMeter]
 have split : (K+3*(leaves T).length+16)*cs.length=(K+3*(leaves T).length+7)*cs.length+9*cs.length := by rw [←Nat.add_mul];congr 1;omega
 rw [split]
 omega

theorem run_children_recursive (actual : Ordinary) (forestFee : ForestQuery→Nat) (agreementFee : Forest→Nat) (T S : Tree) (q : Nat) (cs : List Child) :
 (runChildrenMeter actual forestFee agreementFee T S q cs).recursiveWork=
 ((runChildrenMeter actual forestFee agreementFee T S q cs).calls.map forestFee).sum :=
 children_answers_recursive actual forestFee T q cs
end Universal233.Rule5SelectedLocalWork
