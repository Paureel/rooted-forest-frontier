import QueryMass
import CurrentQuery
import GroupCostProof
namespace Universal233.GroupedFullQuery
open RMAF ForestState ForestGroups PaidQueries ForestMinCompletion
abbrev Forest := List (List Nat)
abbrev Ordinary := Tree → Tree → Nat → Option Forest
structure Problem where
 key : List Nat
 target : Option Tree
 sources : List Tree
 deriving DecidableEq, Repr

def valid (p : Problem) (F : Forest) : Prop := agrees p.target p.sources F=true
def cost (p : Problem) (F : Forest) : Nat := additionalCost p.sources F
def least (p : Problem) (F : Forest) : Prop := ∀ G,valid p G → cost p F≤cost p G

def prepareOne (p : Problem) : Option (Job Problem Forest) :=
 match ForestPretest01.pretest01 p.target p.sources with
 | .refused => none
 | .found F => some (.resolved p (cost p F) F)
 | .rejected => some (.hard p)

def prepare : List Problem → Option (List (Job Problem Forest))
 | [] => some []
 | p::ps => do let j ← prepareOne p;let js ← prepare ps;pure (j::js)

def Planned : Job Problem Forest → Prop
 | .resolved p c F => valid p F ∧ c=cost p F ∧ least p F ∧ c≤1
 | .hard p => proper p.target p.sources=true ∧ ∀ G,valid p G → 2≤cost p G

theorem prepareOne_spec (p : Problem) (j : Job Problem Forest) (h : prepareOne p=some j) :
 j.problem=p ∧ Planned j := by
 cases hp : ForestPretest01.pretest01 p.target p.sources with
 | refused => simp [prepareOne,hp] at h
 | found F =>
   have he : Job.resolved p (cost p F) F=j := by simpa [prepareOne,hp] using h
   subst j
   have hs := ForestPretest01.found_globally_minimum p.target p.sources F hp
   exact ⟨rfl,hs.1,rfl,hs.2.2,hs.2.1⟩
 | rejected =>
   have he : Job.hard p=j := by simpa [prepareOne,hp] using h
   subst j
   exact ⟨rfl,ForestPretest01.rejected_lower_bound p.target p.sources hp⟩

theorem prepareOne_none_iff (p : Problem) : prepareOne p=none ↔ proper p.target p.sources=false := by
 rw [←ForestPretest01.refused_iff p.target p.sources]
 cases hp : ForestPretest01.pretest01 p.target p.sources <;> simp [prepareOne,hp]

theorem prepareOne_exists (p : Problem) (hp : proper p.target p.sources=true) :
 ∃ j,prepareOne p=some j := by
 cases h : prepareOne p with
 | none => have hf := (prepareOne_none_iff p).1 h;simp [hp] at hf
 | some j => exact ⟨j,rfl⟩

theorem prepare_spec (ps : List Problem) (js : List (Job Problem Forest)) (h : prepare ps=some js) :
 js.map Job.problem=ps ∧ ∀ j∈js,Planned j := by
 induction ps generalizing js with
 | nil =>
   have he : js=[] := by simpa [prepare] using h.symm
   subst js
   exact ⟨rfl,by simp⟩
 | cons p ps ih =>
   cases hp : prepareOne p with
   | none => simp [prepare,hp] at h
   | some j =>
     cases ht : prepare ps with
     | none => simp [prepare,hp,ht] at h
     | some ks =>
       have he : js=j::ks := by simpa [prepare,hp,ht] using h.symm
       subst js
       obtain ⟨eq,plan⟩ := prepareOne_spec p j hp
       obtain ⟨eqs,plans⟩ := ih ks ht
       exact ⟨by simp [eq,eqs],by intro k hk;rcases List.mem_cons.1 hk with rfl|hk;exact plan;exact plans k hk⟩

theorem prepare_exists (ps : List Problem) (hp : ∀ p∈ps,proper p.target p.sources=true) :
 ∃ js,prepare ps=some js := by
 induction ps with
 | nil => exact ⟨[],rfl⟩
 | cons p ps ih =>
   obtain ⟨j,hj⟩ := prepareOne_exists p (hp p (by simp))
   obtain ⟨js,hjs⟩ := ih (fun p hp' => hp p (by simp [hp']))
   exact ⟨j::js,by simp [prepare,hj,hjs]⟩

def groupProblem (T : Option Tree) (ss : List Tree) (U : List Nat) : Problem :=
 ⟨U,localTarget T U,owned ss U⟩
def groupProblems (T : Option Tree) (ss : List Tree) (Q : Forest) : List Problem :=
 Q.map (groupProblem T ss)

theorem prepare_groups_exists (T : Option Tree) (ss : List Tree) (Q : Forest)
 (hp : proper T ss=true) (hq : partitionCheck (labels T) Q=true) (own : Owns ss Q) :
 ∃ js,prepare (groupProblems T ss Q)=some js := by
 apply prepare_exists
 intro p hm
 obtain ⟨U,hU,rfl⟩ := List.mem_map.1 hm
 exact local_proper T ss Q hp hq own U hU
end Universal233.GroupedFullQuery
