import Partition
namespace Universal233.CherryBranching
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent

/-- Enumerate each original cherry once, including its original parent address.
The leaf order is the actual child order; no sorting/root sentinel is inserted. -/
def cherries : Tree → List (RMAF.Vertex × Nat × Nat)
 | .leaf _ => []
 | .node (.leaf a) (.leaf b) => [([],a,b)]
 | .node l r =>
   (cherries l).map (fun (p,a,b) => (false::p,a,b)) ++
   (cherries r).map (fun (p,a,b) => (true::p,a,b))

theorem cherries_sound (T : Tree) (p : RMAF.Vertex) (a b : Nat)
 (h : (p,a,b) ∈ cherries T) : CherryAt T p a b := by
 induction T generalizing p with
 | leaf x => simp [cherries] at h
 | node l r ihl ihr =>
   cases l with
   | leaf x =>
     cases r with
     | leaf y =>
       have he : p = [] ∧ a = x ∧ b = y := by simpa [cherries] using h
       rcases he with ⟨rfl,rfl,rfl⟩
       rfl
     | node u v =>
       simp only [cherries,List.mem_append,List.mem_map] at h
       rcases h with ⟨⟨q,c,d⟩,hq,he⟩ | ⟨⟨q,c,d⟩,hq,he⟩
       · simp [cherries] at hq
       · cases he
         exact ihr q hq
   | node u v =>
     simp only [cherries,List.mem_append,List.mem_map] at h
     rcases h with ⟨⟨q,c,d⟩,hq,he⟩ | ⟨⟨q,c,d⟩,hq,he⟩
     · cases he; exact ihl q hq
     · cases he; exact ihr q hq

theorem cherries_complete (T : Tree) (p : RMAF.Vertex) (a b : Nat)
 (h : CherryAt T p a b) : (p,a,b) ∈ cherries T := by
 induction p generalizing T with
 | nil =>
   simp [CherryAt,subtree] at h
   subst T
   simp [cherries]
 | cons s p ih =>
   cases T with
   | leaf x => simp [CherryAt,subtree] at h
   | node l r =>
     cases l with
     | leaf x =>
       cases r with
       | leaf y => cases s <;> cases p <;> simp [CherryAt,subtree] at h
       | node u v =>
         cases s
         · cases p <;> simp [CherryAt,subtree] at h
         · have hh := ih (.node u v) h
           exact List.mem_append_right _ (List.mem_map.2 ⟨(p,a,b),hh,rfl⟩)
     | node u v =>
       cases s
       · exact List.mem_append_left _ (List.mem_map.2 ⟨(p,a,b),ih _ h,rfl⟩)
       · exact List.mem_append_right _ (List.mem_map.2 ⟨(p,a,b),ih _ h,rfl⟩)

structure Candidate where
 parent : RMAF.Vertex
 a : Nat
 b : Nat
 originalCuts : List RMAF.Vertex
 deriving Repr, DecidableEq

def candidates (T S : Tree) : List Candidate :=
 (cherries T).map fun (p,a,b) => ⟨p,a,b,cuts S a b⟩

inductive Priority where
 | common | one | high | hard2
 deriving Repr, DecidableEq

def rank (n : Nat) : Priority := if n=0 then .common else if n=1 then .one else if 3≤n then .high else .hard2

def select (T S : Tree) : Option (Priority × Candidate) :=
 let cs := candidates T S
 match cs.find? (fun c => c.originalCuts.isEmpty) with
 | some c => some (.common,c)
 | none => match cs.find? (fun c => c.originalCuts.length == 1) with
   | some c => some (.one,c)
   | none => match cs.find? (fun c => 3 ≤ c.originalCuts.length) with
     | some c => some (.high,c)
     | none => cs.head?.map fun c => (.hard2,c)

theorem candidate_sound {T S : Tree} {c : Candidate} (hc : c ∈ candidates T S) :
 CherryAt T c.parent c.a c.b ∧ c.originalCuts = cuts S c.a c.b := by
 obtain ⟨⟨p,a,b⟩,h,he⟩ := List.mem_map.1 hc
 cases he
 exact ⟨cherries_sound T p a b h,rfl⟩

/-- States retain the original source and its permanent component partition.
The forest is executable restrictions, so no suppressed edge is charged. -/
structure Child where
 partition : List (List Nat)
 sourceForest : List Tree
 paid : Nat
 deriving Repr, DecidableEq

def makeChild (S : Tree) (P : List (List Nat)) (paid : Nat) : Child :=
 ⟨P,P.filterMap (fun B => restrict B S),paid⟩

def pendantChild (S : Tree) (a b : Nat) : Child :=
 makeChild S (pendantPartition S a b) (cuts S a b).length

def singletonPartition (S : Tree) (a : Nat) : List (List Nat) :=
 [[a],(leaves S).filter fun x => x != a]

def singletonChild (S : Tree) (a : Nat) : Child := makeChild S (singletonPartition S a) 1

def branches (S : Tree) (a b : Nat) : List Child :=
 [singletonChild S a,singletonChild S b,pendantChild S a b]

def feasible (T S : Tree) (c : Child) (F : List (List Nat)) : Prop :=
 agreement T S F = true ∧ Refines F c.partition

def remaining (budget : Nat) (c : Child) : Option Nat :=
 if c.paid ≤ budget then some (budget-c.paid) else none

theorem pendant_paid (S : Tree) (a b : Nat) :
 (pendantChild S a b).paid = (cuts S a b).length ∧
 (pendantChild S a b).partition.length = (pendantChild S a b).paid+1 := by
 simp [pendantChild,makeChild,partition_length]

theorem endpoint_paid (S : Tree) (a : Nat) : (singletonChild S a).paid = 1 := rfl

theorem budget_exact (budget : Nat) (c : Child) (h : c.paid ≤ budget) :
 remaining budget c = some (budget-c.paid) ∧ c.paid+(budget-c.paid)=budget := by
 simp [remaining,h,Nat.add_sub_of_le h]

/-- Exact residual-cost consuming interface. Each child solver has its own IH,
and no history or output claim is supplied by a global recursive solver. -/
def ExactChild (T S : Tree) (c : Child) (G : List (List Nat)) : Prop :=
 feasible T S c G ∧ ∀ F, feasible T S c F → G.length ≤ F.length

theorem child_minimum_consumes {T S : Tree} {c : Child} {G F : List (List Nat)}
 (ih : ExactChild T S c G) (hf : feasible T S c F) :
 agreement T S G = true ∧ Refines G c.partition ∧ G.length ≤ F.length :=
 ⟨ih.1.1,ih.1.2,ih.2 F hf⟩
end Universal233.CherryBranching
