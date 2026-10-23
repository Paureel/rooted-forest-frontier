import SetupAtoms
import SelectorBuilder
namespace Universal233.Rule5RemainingLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5PendantLocalWork Rule5PaidSelector

/-- Tree-to-leaf equality inspects only the outer constructor and label. -/
def leafEqMeter (T : Tree) (x : Nat) : Measured Bool := ⟨decide (T=.leaf x),3⟩

def parseBottomMeter (S : Tree) (w : RMAF.Vertex) (sa sc sb : Bool) (a b c : Nat) : Measured (Option Tree) :=
 let z:=subtreeMeter S w
 let finish : Measured (Option Tree):=
  match z.value with
  | none=>⟨none,1⟩
  | some Z=>
    match unorient sb Z with
    | none=>⟨none,2⟩
    | some (V,B)=>
      match unorient sc V with
      | none=>⟨none,4⟩
      | some (A,C)=>
        match unorient sa A with
        | none=>⟨none,6⟩
        | some (L,X)=>
          let eb:=leafEqMeter B b;let ec:=leafEqMeter C c;let ea:=leafEqMeter L a
          ⟨if eb.value && ec.value && ea.value then some X else none,eb.work+ec.work+ea.work+9⟩
 ⟨finish.value,z.work+finish.work+1⟩

theorem parse_bottom_value (S : Tree) (w : RMAF.Vertex) (sa sc sb : Bool) (a b c : Nat) :
 (parseBottomMeter S w sa sc sb a b c).value=parseBottom S w sa sc sb a b c := by
 simp only [parseBottomMeter,subtree_value,parseBottom]
 cases h:subtree S w with
 | none=>rfl
 | some Z=>
   cases Z with
   | leaf x=>rfl
   | node l r=>
     cases sb <;> simp only [unorient,Bool.false_eq_true,ite_false,ite_true,Option.bind_some]
     all_goals split <;> try rfl
     all_goals rename_i V B hV
     all_goals cases sc <;> simp only [unorient,Bool.false_eq_true,ite_false,ite_true,Option.bind_some]
     all_goals split <;> try rfl
     all_goals rename_i A C hA
     all_goals cases sa <;> simp [unorient,leafEqMeter,Bool.decide_and,and_assoc]

theorem parse_bottom_work (S : Tree) (w : RMAF.Vertex) (sa sc sb : Bool) (a b c : Nat) :
 (parseBottomMeter S w sa sc sb a b c).work≤2*w.length+20 := by
 have z:=subtree_work S w
 simp only [parseBottomMeter]
 split <;> try (dsimp only;omega)
 split <;> try (dsimp only;omega)
 split <;> try (dsimp only;omega)
 split <;> dsimp only [leafEqMeter] <;> omega

def fmMeter {α β : Type} (f : α→Measured (List β)) : List α→Measured (List β)
 | []=>⟨[],1⟩
 | x::xs=>let a:=f x;let r:=fmMeter f xs;⟨a.value++r.value,a.work+r.work+a.value.length+3⟩

theorem fm_value {α β : Type} (f : α→Measured (List β)) (xs : List α) :
 (fmMeter f xs).value=xs.flatMap (fun x=>(f x).value) := by
 induction xs <;> simp_all [fmMeter]

theorem fm_work {α β : Type} (f : α→Measured (List β)) (xs : List α) (K M : Nat)
 (cost : ∀x,x∈xs→(f x).work≤K) (size : ∀x,x∈xs→(f x).value.length≤M) :
 (fmMeter f xs).work≤(K+M+3)*xs.length+1 := by
 induction xs with
 | nil=>simp [fmMeter]
 | cons x xs ih=>
  have a:=cost x (by simp);have b:=size x (by simp)
  have r:=ih (fun y h=>cost y (by simp [h])) (fun y h=>size y (by simp [h]))
  simp only [fmMeter,List.length_cons,Nat.mul_succ];omega

theorem fm_size {α β : Type} (f : α→Measured (List β)) (xs : List α) (M : Nat)
 (size : ∀x,x∈xs→(f x).value.length≤M) : (fmMeter f xs).value.length≤M*xs.length := by
 induction xs with
 | nil=>simp [fmMeter]
 | cons x xs ih=>
  have a:=size x (by simp);have r:=ih (fun y h=>size y (by simp [h]))
  simp only [fmMeter,List.length_cons,List.length_append,Nat.mul_succ];omega

def pairRowsMeter (S : Tree) (w : RMAF.Vertex) (sa sc sb : Bool) (a b c : Nat) : Measured (List BottomData) :=
 fmMeter (fun xy=>let p:=parseBottomMeter S w sa sc sb xy.1 xy.2 c
  ⟨match p.value with | none=>[] | some X=>[⟨w,sa,sc,sb,xy.1,xy.2,X⟩],p.work+2⟩) [(a,b),(b,a)]

def rowAtMeter (S : Tree) (w : RMAF.Vertex) (a b c : Nat) : Measured (List BottomData) :=
 fmMeter (fun sa=>fmMeter (fun sc=>fmMeter (fun sb=>pairRowsMeter S w sa sc sb a b c)
  [false,true]) [false,true]) [false,true]

def rowsMeter (S : Tree) (a b c : Nat) : Measured (List BottomData) :=
 let v:=verticesMeter S;let r:=fmMeter (fun w=>rowAtMeter S w a b c) v.value
 ⟨r.value,v.work+r.work+1⟩

theorem pair_rows_value (S : Tree) (w : RMAF.Vertex) (sa sc sb : Bool) (a b c : Nat) :
 (pairRowsMeter S w sa sc sb a b c).value=
 [(a,b),(b,a)].filterMap (fun xy=>(parseBottom S w sa sc sb xy.1 xy.2 c).map
  (fun X=>(⟨w,sa,sc,sb,xy.1,xy.2,X⟩:BottomData))) := by
 simp only [pairRowsMeter,fm_value,List.flatMap_cons,List.flatMap_nil,List.filterMap_cons,List.filterMap_nil,parse_bottom_value]
 cases ha:parseBottom S w sa sc sb a b c <;> cases hb:parseBottom S w sa sc sb b a c <;> simp [ha,hb]

theorem rows_value (S : Tree) (a b c : Nat) : (rowsMeter S a b c).value=rows S a b c := by
 simp only [rowsMeter,rowAtMeter,fm_value,vertices_value,pair_rows_value,rows]

end Universal233.Rule5RemainingLocalWork
