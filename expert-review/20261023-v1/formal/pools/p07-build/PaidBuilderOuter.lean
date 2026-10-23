import PaidAddresses
namespace Universal233.Rule5RemainingLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5PendantLocalWork Rule5PaidSelector Rule5Classification Rule5FinalClassification Case322PaidGuard

structure LiteralCall where
 row : BottomData
 core : Tree
 qa : RMAF.Vertex
 ub : RMAF.Vertex
 selection : BadSelection
 u : RMAF.Vertex
 v : RMAF.Vertex
 deriving DecidableEq, Repr

/-- Exact decision-input frontier. This fee is NOT discharged here; LiteralProps
still needs its own source meter. No paid-arm polynomial is asserted without it. -/
def oneCalls (T : Tree) (d : BadSelection) (u v : RMAF.Vertex) (R : BottomData) : List LiteralCall :=
 match subtree T v,leafAddress? T R.a,leafAddress? T R.b with
 | some C,some qa,some ub=>[⟨R,C,qa,ub,d,u,v⟩]
 | _,_,_=>[]

def buildOneMeter (fee : LiteralCall→Nat) (T S : Tree) (a b : Nat) (d : BadSelection)
 (u v : RMAF.Vertex) (R : BottomData) : Measured (Option (LiteralGeometry T S)) :=
 bump ((subtreeMeter T v).work+(leafAddressMeter T R.a).work+(leafAddressMeter T R.b).work+5) <|
 match hc:subtree T v,leafAddress? T R.a,leafAddress? T R.b with
 | some C,some qa,some ub=>
   bump (fee ⟨R,C,qa,ub,d,u,v⟩+1) <|
   if h:LiteralProps T S a b d u v R C qa ub then ⟨some (ofProps hc h),1⟩ else ⟨none,1⟩
 | _,_,_=>⟨none,1⟩

theorem build_one_value (fee : LiteralCall→Nat) (T S : Tree) (a b : Nat) (d : BadSelection)
 (u v : RMAF.Vertex) (R : BottomData) :
 (buildOneMeter fee T S a b d u v R).value=buildOne T S a b d u v R := by
 simp only [buildOneMeter,bump_value,buildOne]
 split
 · rename_i C qa ub hc ha hb
   symm
   split
   · rename_i C' qa' ub' hc' ha' hb'
     have ec : C'=C:=Option.some.inj (hc'.symm.trans hc)
     have ea : qa'=qa:=Option.some.inj (ha'.symm.trans ha)
     have eb : ub'=ub:=Option.some.inj (hb'.symm.trans hb)
     subst C';subst qa';subst ub'
     symm
     simp only [bump_value]
     by_cases h:LiteralProps T S a b d u v R C qa ub
     · simp only [dite_eq_left h]
     · simp only [dite_eq_right h]
   · rename_i bad
     exact False.elim (bad C qa ub hc ha hb)
 · rename_i bad
   split
   · rename_i C qa ub hc ha hb
     exact False.elim (bad C qa ub hc ha hb)
   · rfl

def oneBudget (n m K : Nat) :=2*m+2*leafAddressBudget n+K+8

theorem build_one_work (fee : LiteralCall→Nat) (T S : Tree) (a b : Nat) (d : BadSelection)
 (u v : RMAF.Vertex) (R : BottomData) (K : Nat)
 (primitive : ∀j,j∈oneCalls T d u v R→fee j≤K) :
 (buildOneMeter fee T S a b d u v R).work≤oneBudget (leaves T).length v.length K := by
 have st:=subtree_work T v;have aa:=leaf_address_work T R.a;have ab:=leaf_address_work T R.b
 unfold oneBudget
 simp only [buildOneMeter,bump_work]
 split
 · rename_i C qa ub hc ha hb
   have mem : (⟨R,C,qa,ub,d,u,v⟩:LiteralCall)∈oneCalls T d u v R := by simp [oneCalls,hc,ha,hb]
   have fe:=primitive _ mem
   simp only [bump_work]
   split <;> dsimp only <;> omega
 · dsimp only;omega

/-- Uniform source request domain records actual row membership and the three
successful native lookup equations, including refused LiteralProps decisions. -/
def LiteralCallDomain (T S : Tree) (a b : Nat) (d : BadSelection) (u v : RMAF.Vertex) (j : LiteralCall) : Prop :=
 j.row∈rows S a b d.c ∧ subtree T v=some j.core ∧
 leafAddress? T j.row.a=some j.qa ∧ leafAddress? T j.row.b=some j.ub ∧ j.selection=d ∧ j.u=u ∧ j.v=v

theorem one_calls_domain (T S : Tree) (a b : Nat) (d : BadSelection) (u v : RMAF.Vertex)
 (R : BottomData) (row : R∈rows S a b d.c) {j : LiteralCall} (mem : j∈oneCalls T d u v R) :
 LiteralCallDomain T S a b d u v j := by
 unfold oneCalls at mem
 split at mem
 · rename_i C qa ub hc ha hb
   have eq : j=⟨R,C,qa,ub,d,u,v⟩:=by simpa using mem
   subst j
   exact ⟨row,hc,ha,hb,rfl,rfl,rfl⟩
 · simp at mem

/-- Exact first-success evaluation; suffix rows are skipped after a success. -/
def findBuilderMeter {α β : Type} (f : α→Measured (Option β)) : List α→Measured (Option β)
 | []=>⟨none,1⟩
 | x::xs=>let a:=f x
           match a.value with
           | some y=>⟨some y,a.work+2⟩
           | none=>let r:=findBuilderMeter f xs;⟨r.value,a.work+r.work+2⟩

theorem find_builder_value {α β : Type} (f : α→Measured (Option β)) (xs : List α) :
 (findBuilderMeter f xs).value=xs.findSome? (fun x=>(f x).value) := by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>simp only [findBuilderMeter,List.findSome?_cons];split <;> simp_all

theorem find_builder_work {α β : Type} (f : α→Measured (Option β)) (xs : List α) (K : Nat)
 (cost : ∀x,x∈xs→(f x).work≤K) :
 (findBuilderMeter f xs).work≤(K+2)*xs.length+1 := by
 induction xs with
 | nil=>simp [findBuilderMeter]
 | cons x xs ih=>
  have a:=cost x (by simp);have r:=ih (fun y hy=>cost y (by simp [hy]))
  simp only [findBuilderMeter,List.length_cons,Nat.mul_succ]
  split <;> dsimp only <;> omega

def secondBuilderMeter (fee : LiteralCall→Nat) (T S : Tree) (a b : Nat) (d : BadSelection)
 (u v : RMAF.Vertex) : Measured (Option (LiteralGeometry T S)) :=
 let rs:=rowsMeter S a b d.c
 let out:=findBuilderMeter (buildOneMeter fee T S a b d u v) rs.value
 ⟨out.value,rs.work+out.work+1⟩

theorem second_builder_value (fee : LiteralCall→Nat) (T S : Tree) (a b : Nat) (d : BadSelection)
 (u v : RMAF.Vertex) :
 (secondBuilderMeter fee T S a b d u v).value=buildForSecond T S a b d u v := by
 simp only [secondBuilderMeter,find_builder_value,build_one_value,rows_value,buildForSecond]

def secondBuilderBudget (nt ns m K : Nat) :=rowsBudget ns+(oneBudget nt m K+2)*(32*ns)+2

theorem second_builder_work (fee : LiteralCall→Nat) (T S : Tree) (a b : Nat) (d : BadSelection)
 (u v : RMAF.Vertex) (K : Nat)
 (primitive : ∀j,LiteralCallDomain T S a b d u v j→fee j≤K) :
 (secondBuilderMeter fee T S a b d u v).work≤secondBuilderBudget (leaves T).length (leaves S).length v.length K := by
 have rs:=rows_work S a b d.c;have count:=rows_count S a b d.c
 have f:=find_builder_work (buildOneMeter fee T S a b d u v) (rowsMeter S a b d.c).value
  (oneBudget (leaves T).length v.length K) (by
   intro R hr
   apply build_one_work
   intro j hj
   apply primitive j
   apply one_calls_domain T S a b d u v R (by rw [←rows_value];exact hr) hj)
 have scaled:=Nat.mul_le_mul_left (oneBudget (leaves T).length v.length K+2) count
 simp only [secondBuilderMeter,secondBuilderBudget];omega
end Universal233.Rule5RemainingLocalWork
