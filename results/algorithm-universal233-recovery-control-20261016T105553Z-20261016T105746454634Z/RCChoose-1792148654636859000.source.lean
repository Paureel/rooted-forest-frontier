import RCMixed
namespace OrdinaryDispatch.RecoveryControlBits
open Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryInitialBits

inductive Refusal where
 | empty | homogeneousCherry | noCherry
 deriving DecidableEq,Repr
inductive BitChoice where
 | finish
 | one : BitGroup→BitChoice
 | two : BitGroup→BitGroup→BitChoice
 | refuse : Refusal→BitChoice
 deriving DecidableEq,Repr

def viewChoice : BitChoice→Choice
 | .finish=>.finish
 | .one g=>.one (viewGroup g)
 | .two a b=>.two (viewGroup a) (viewGroup b)
 | .refuse .empty=>.refuse "empty current source"
 | .refuse .homogeneousCherry=>.refuse "unnormalized homogeneous cherry"
 | .refuse .noCherry=>.refuse "no mixed cherry in multicolor source"

def ChoiceCaps (W N : Nat) : BitChoice→Prop
 | .one g=>GroupCap W N g
 | .two a b=>GroupCap W N a ∧ GroupCap W N b
 | _=>True

def chooseCore (W : Nat) (gs : List BitGroup) (t : BitTree) : Charged BitChoice :=
 match gs with
 | []=>⟨.refuse .empty,4⟩
 | first::_=>
  let uniform:=allColor first.color gs
  if uniform.value then ⟨.finish,uniform.work+8⟩ else
   let found:=findUnique W gs gs
   match found.value with
   | some g=>⟨.one g,uniform.work+found.work+12⟩
   | none=>
    let cherry:=mixedBits t
    match cherry.value with
    | none=>⟨.refuse .noCherry,uniform.work+found.work+cherry.work+16⟩
    | some (a,b)=>
     let e:=ownedEqual a.color b.color
     if e.value then
      let c:=closePair (a,b)
      ⟨.refuse .homogeneousCherry,uniform.work+found.work+cherry.work+e.work+c.work+16⟩
     else ⟨.two a b,uniform.work+found.work+cherry.work+e.work+16⟩

def chooseBits (W : Nat) (t : BitTree) : Charged BitChoice :=
 let gs:=groupsBits t;let r:=chooseCore W gs.value t;let c:=closeGroups gs.value
 ⟨r.value,gs.work+r.work+c.work+12⟩

theorem chooseCore_value (W : Nat) (t : BitTree) (fits : (rawGroups t).length<2^W) :
 viewChoice (chooseCore W (rawGroups t) t).value=CoreProgram.choose (viewTree t) := by
 have fv:=findUnique_value W (rawGroups t) (rawGroups t) fits
 have cv:((mixedBits t).value.map viewPair)=mixedCherry (viewTree t):=by simp
 cases hg:rawGroups t with
 | nil=>simp only [chooseCore,hg,viewChoice,CoreProgram.choose,←rawGroups_view,hg,List.map_nil]
 | cons first rest=>
  simp only [hg,List.map_cons] at fv
  simp only [chooseCore,hg,allColor_value,CoreProgram.choose,←rawGroups_view,hg,List.map_cons]
  by_cases uniform:((first::rest).map viewGroup).all (fun g=>g.color==decode first.color)=true
  · simpa [viewChoice,viewGroup,uniform] using (rfl : Choice.finish=Choice.finish)
  · simp only [uniform,ite_false]
    rw [←fv]
    cases hf:(findUnique W (first::rest) (first::rest)).value with
    | some g=>simp [hf,viewChoice]
    | none=>
     simp only [hf,Option.map_none]
     rw [←cv]
     cases hc:(mixedBits t).value with
     | none=>simp [hc,viewChoice]
     | some p=>
      rcases p with ⟨a,b⟩
      simp only [hc,Option.map_some,viewPair]
      cases he:ownedEqual a.color b.color |>.value <;> simp [he,ownedEqual_value,viewChoice,viewGroup] at *

@[simp] theorem chooseBits_value (W : Nat) (t : BitTree) (fits : (rawGroups t).length<2^W) :
 viewChoice (chooseBits W t).value=CoreProgram.choose (viewTree t) := by
 simpa only [chooseBits,groupsBits_value] using chooseCore_value W t fits

theorem chooseCore_caps (W N : Nat) (gs : List BitGroup) (t : BitTree)
 (caps : GroupCaps W N gs) (words : TreeWords W t) (size : footprint (viewTree t)≤N) :
 ChoiceCaps W N (chooseCore W gs t).value := by
 cases gs with
 | nil=>trivial
 | cons first rest=>
  simp only [chooseCore]
  split
  · trivial
  · cases hf:(findUnique W (first::rest) (first::rest)).value with
    | some g=>
     simp only [hf,ChoiceCaps]
     exact caps g (findUnique_mem W _ _ g hf)
    | none=>
     simp only [hf]
     cases hc:(mixedBits t).value with
     | none=>trivial
     | some p=>
      rcases p with ⟨a,b⟩
      have c:=mixedBits_caps W N t words size a b hc
      simp only [hc]
      split
      · trivial
      · exact c

theorem chooseBits_caps (W N : Nat) (t : BitTree) (words : TreeWords W t) (size : footprint (viewTree t)≤N) :
 ChoiceCaps W N (chooseBits W t).value := by
 simpa only [chooseBits,groupsBits_value] using chooseCore_caps W N (rawGroups t) t (rawGroups_caps W N t words size) words size

def choiceCells : BitChoice→Nat
 | .one g=>groupCells g+1
 | .two a b=>groupCells a+groupCells b+1
 | _=>1

theorem choiceCells_cap (W N : Nat) (c : BitChoice) (caps : ChoiceCaps W N c) :
 choiceCells c≤2*((W+4)*N)+1 := by
 cases c with
 | finish=>simp [choiceCells]
 | refuse r=>simp [choiceCells]
 | one g=>have h:=group_cells_cap W N g caps;simp only [choiceCells];omega
 | two a b=>have x:=group_cells_cap W N a caps.1;have y:=group_cells_cap W N b caps.2;simp only [choiceCells];omega
end OrdinaryDispatch.RecoveryControlBits
