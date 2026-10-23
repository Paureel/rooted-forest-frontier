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
   cases hb:unorient sb Z with
   | none=>simp [hb]
   | some pair=>
     obtain ⟨V,B⟩:=pair
     cases hc:unorient sc V with
     | none=>simp [hb,hc]
     | some pair=>
       obtain ⟨A,C⟩:=pair
       cases ha:unorient sa A with
       | none=>simp [hb,hc,ha]
       | some pair=>
         obtain ⟨L,X⟩:=pair
         simp [hb,hc,ha,leafEqMeter,and_assoc]

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
  ⟨match p.value with | none=>[] | some X=>[(⟨w,sa,sc,sb,xy.1,xy.2,X⟩:BottomData)],p.work+2⟩) [(a,b),(b,a)]

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

theorem pair_rows_size (S : Tree) (w : RMAF.Vertex) (sa sc sb : Bool) (a b c : Nat) :
 (pairRowsMeter S w sa sc sb a b c).value.length≤2 := by
 have h:=fm_size (fun xy : Nat×Nat=>let p:=parseBottomMeter S w sa sc sb xy.1 xy.2 c
  ⟨match p.value with | none=>[] | some X=>[(⟨w,sa,sc,sb,xy.1,xy.2,X⟩:BottomData)],p.work+2⟩)
  [(a,b),(b,a)] 1 (by intro xy _;dsimp only;split <;> simp)
 simpa only [pairRowsMeter,List.length_cons,List.length_nil] using h

theorem pair_rows_work (S : Tree) (w : RMAF.Vertex) (sa sc sb : Bool) (a b c : Nat) :
 (pairRowsMeter S w sa sc sb a b c).work≤4*w.length+55 := by
 have h:=fm_work (fun xy : Nat×Nat=>let p:=parseBottomMeter S w sa sc sb xy.1 xy.2 c
  ⟨match p.value with | none=>[] | some X=>[(⟨w,sa,sc,sb,xy.1,xy.2,X⟩:BottomData)],p.work+2⟩)
  [(a,b),(b,a)] (2*w.length+22) 1
  (by intro xy _;dsimp only;have:=parse_bottom_work S w sa sc sb xy.1 xy.2 c;omega)
  (by intro xy _;dsimp only;split <;> simp)
 simp only [List.length_cons,List.length_nil] at h
 change (fmMeter _ _).work≤_
 omega

theorem row_at_size (S : Tree) (w : RMAF.Vertex) (a b c : Nat) :
 (rowAtMeter S w a b c).value.length≤16 := by
 have inner (sa sc : Bool) :=fm_size (fun sb=>pairRowsMeter S w sa sc sb a b c)
  [false,true] 2 (fun sb _=>pair_rows_size S w sa sc sb a b c)
 have middle (sa : Bool) :=fm_size (fun sc=>fmMeter (fun sb=>pairRowsMeter S w sa sc sb a b c) [false,true])
  [false,true] 4 (fun sc _=>inner sa sc)
 have outer:=fm_size (fun sa=>fmMeter (fun sc=>fmMeter (fun sb=>pairRowsMeter S w sa sc sb a b c) [false,true]) [false,true])
  [false,true] 8 (fun sa _=>middle sa)
 exact outer

theorem row_at_work (S : Tree) (w : RMAF.Vertex) (a b c : Nat) :
 (rowAtMeter S w a b c).work≤32*w.length+600 := by
 have inner (sa sc : Bool) :=fm_work (fun sb=>pairRowsMeter S w sa sc sb a b c)
  [false,true] (4*w.length+55) 2 (fun sb _=>pair_rows_work S w sa sc sb a b c) (fun sb _=>pair_rows_size S w sa sc sb a b c)
 have innerS (sa sc : Bool) :=fm_size (fun sb=>pairRowsMeter S w sa sc sb a b c)
  [false,true] 2 (fun sb _=>pair_rows_size S w sa sc sb a b c)
 have middle (sa : Bool) :=fm_work (fun sc=>fmMeter (fun sb=>pairRowsMeter S w sa sc sb a b c) [false,true])
  [false,true] ((4*w.length+55+2+3)*2+1) 4 (fun sc _=>inner sa sc) (fun sc _=>innerS sa sc)
 have middleS (sa : Bool) :=fm_size (fun sc=>fmMeter (fun sb=>pairRowsMeter S w sa sc sb a b c) [false,true])
  [false,true] 4 (fun sc _=>innerS sa sc)
 have outer:=fm_work (fun sa=>fmMeter (fun sc=>fmMeter (fun sb=>pairRowsMeter S w sa sc sb a b c) [false,true]) [false,true])
  [false,true] ((((4*w.length+55+2+3)*2+1)+4+3)*2+1) 8 (fun sa _=>middle sa) (fun sa _=>middleS sa)
 change (fmMeter _ _).work≤_
 simp only [List.length_cons,List.length_nil] at outer
 omega

def rowsBudget (n : Nat) :=64*n*n+(32*n+619)*(2*n)+2

theorem rows_work (S : Tree) (a b c : Nat) :
 (rowsMeter S a b c).work≤rowsBudget (leaves S).length := by
 have v:=vertices_work S;have vc:=vertices_count S
 have r:=fm_work (fun w=>rowAtMeter S w a b c) (verticesMeter S).value
  (32*(leaves S).length+600) 16
  (by intro w hw;have:=row_at_work S w a b c;have:=vertices_address S hw;omega)
  (fun w _=>row_at_size S w a b c)
 have scaled:=Nat.mul_le_mul_left (32*(leaves S).length+600+16+3)
  (show (verticesMeter S).value.length≤2*(leaves S).length by rw [vertices_value];omega)
 simp only [rowsMeter,rowsBudget]
 simp only [Nat.add_assoc,Nat.reduceAdd] at scaled
 omega

theorem rows_count (S : Tree) (a b c : Nat) : (rowsMeter S a b c).value.length≤32*(leaves S).length := by
 have r:=fm_size (fun w=>rowAtMeter S w a b c) (verticesMeter S).value 16 (fun w _=>row_at_size S w a b c)
 have v:=vertices_count S
 simp only [rowsMeter,vertices_value] at r ⊢
 omega

end Universal233.Rule5RemainingLocalWork
