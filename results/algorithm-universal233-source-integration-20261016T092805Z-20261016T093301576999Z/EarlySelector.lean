import CommonDispatch
import CherryDispatch
import Rule4Dispatch
namespace OrdinaryDispatch.FastOrdinary
open RMAF ForestState Universal233 Universal233.CherryBranching

inductive Early (T S : Tree) where
 | common (reverse : Bool) (c : Candidate)
 | one (reverse : Bool) (c : Candidate)
 | high (reverse : Bool) (c : Candidate)
 | rule4Forward (s : Rule4.Choice T S)
 | rule4Reverse (s : Rule4.Choice S T)
 | hard2 (c d : Candidate)
 | refused

/-- Both orientations are inspected before advancing a source priority.
Rule4 is tested only after both saved cherry selectors are hard2. -/
def early (T S : Tree) : Early T S :=
 match select T S,select S T with
 | some (.common,c),_ => .common false c
 | _,some (.common,d) => .common true d
 | some (.one,c),_ => .one false c
 | _,some (.one,d) => .one true d
 | some (.high,c),_ => .high false c
 | _,some (.high,d) => .high true d
 | some (.hard2,c),some (.hard2,d) =>
   match Rule4.select T S with
   | some s => .rule4Forward s
   | none => match Rule4.select S T with
     | some s => .rule4Reverse s
     | none => .hard2 c d
 | _,_ => .refused

def Oriented (reverse : Bool) (T S : Tree) : Tree×Tree := if reverse then (S,T) else (T,S)

def EarlySound (T S : Tree) : Early T S → Prop
 | .common r c => select (Oriented r T S).1 (Oriented r T S).2=some (.common,c)
 | .one r c => select (Oriented r T S).1 (Oriented r T S).2=some (.one,c)
 | .high r c => select (Oriented r T S).1 (Oriented r T S).2=some (.high,c)
 | .rule4Forward s => Rule4.select T S=some s
 | .rule4Reverse s => Rule4.select S T=some s
 | .hard2 c d => select T S=some (.hard2,c) ∧ select S T=some (.hard2,d) ∧
   Rule4.select T S=none ∧ Rule4.select S T=none
 | .refused => True

theorem early_sound (T S : Tree) : EarlySound T S (early T S) := by
 cases hf : select T S with
 | none =>
   cases hr : select S T with
   | none => simp [early,hf,hr,EarlySound]
   | some pair =>
     obtain ⟨pr,c⟩ := pair
     cases pr <;> simp [early,hf,hr,EarlySound,Oriented]
 | some pair =>
   obtain ⟨pr,c⟩ := pair
   cases hr : select S T with
   | none => cases pr <;> simp [early,hf,hr,EarlySound,Oriented]
   | some pair =>
     obtain ⟨rev,d⟩ := pair
     cases pr <;> cases rev <;> simp [early,hf,hr,EarlySound,Oriented]
     cases r4 : Rule4.select T S with
     | some s => simp [r4,EarlySound]
     | none =>
       cases r4r : Rule4.select S T <;> simp [r4,r4r,EarlySound,hf,hr]

theorem early_not_refused {T S : Tree} {x y : Priority×Candidate}
 (hf : select T S=some x) (hr : select S T=some y) : early T S≠.refused := by
 obtain ⟨pr,c⟩ := x
 obtain ⟨rev,d⟩ := y
 cases pr <;> cases rev <;> simp [early,hf,hr]
 cases r4 : Rule4.select T S with
 | some s => simp [r4]
 | none => cases r4r : Rule4.select S T <;> simp [r4,r4r]
end OrdinaryDispatch.FastOrdinary
