import Rule4LiteralChecks

namespace Universal233.Rule4
open RMAF VertexGeometry CoreGraph Integration HardParent BinaryExchange CutRealization

def orderedCherries : Tree → List (Nat × Nat)
  | .leaf _ => []
  | .node l r =>
    (match l,r with | .leaf a,.leaf b => [(a,b),(b,a)] | _,_ => []) ++
      orderedCherries l ++ orderedCherries r

theorem orderedCherries_sound {T : Tree} {a b : Nat}
    (h : (a,b) ∈ orderedCherries T) : HasCherry a b T := by
  induction T with
  | leaf x => simp [orderedCherries] at h
  | node l r il ir =>
    simp only [orderedCherries,List.mem_append,or_assoc] at h
    rcases h with hh | hh | hh
    · cases l with
      | node x y => simp at hh
      | leaf x =>
        cases r with
        | node y z => simp at hh
        | leaf y =>
          have cases : (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by simpa using hh
          rcases cases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact .here
          · exact .swap
    · exact .left (il hh)
    · exact .right (ir hh)

theorem orderedCherries_complete {T : Tree} {a b : Nat} (h : HasCherry a b T) :
    (a,b) ∈ orderedCherries T := by
  induction h with
  | here => simp [orderedCherries]
  | swap => simp [orderedCherries]
  | left h ih => exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr ih)))
  | right h ih => exact List.mem_append.2 (Or.inr ih)

def Priority (T S : Tree) : Prop :=
  (leaves T).Nodup ∧ (leaves S).Nodup ∧ (leaves T).Perm (leaves S) ∧
  (orderedCherries T).all (fun p => !(orderedCherries S).contains p) = true ∧
  (orderedCherries T).all (fun p => (pendantOriginal S p.1 p.2).length != 1) = true ∧
  (orderedCherries S).all (fun p => (pendantOriginal T p.1 p.2).length != 1) = true

instance (T S : Tree) : Decidable (Priority T S) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

structure RawChoice where
  a : Nat
  b : Nat
  c : Nat
  cHead : RMAF.Vertex
  xHead : RMAF.Vertex
  deriving Repr, DecidableEq

def LocalGuard (T S : Tree) (s : RawChoice) : Prop :=
  (s.a,s.b) ∈ orderedCherries T ∧ (s.a,s.c) ∈ orderedCherries S ∧ s.a ≠ s.b ∧
  (pendantOriginal S s.a s.b).Perm [s.cHead,s.xHead] ∧ subtreeLabels S s.cHead = [s.c]

instance (T S : Tree) (s : RawChoice) : Decidable (LocalGuard T S s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Only original source admission guards, never safety/exchange/minimum fields. -/
structure Choice (T S : Tree) where
  raw : RawChoice
  priority : Priority T S
  admission : LocalGuard T S raw

/-- Finite original cherries, both endpoint orders, and the two actual pendant
heads. There is no set-partition search in this selector. -/
def rawChoices (T S : Tree) : List RawChoice :=
  (orderedCherries T).flatMap fun ab =>
    (orderedCherries S).flatMap fun ac =>
      if ab.1 = ac.1 ∧ (pendantOriginal S ab.1 ab.2).length = 2 then
        (pendantOriginal S ab.1 ab.2).flatMap fun q =>
          (pendantOriginal S ab.1 ab.2).map fun r => ⟨ab.1,ab.2,ac.2,q,r⟩
      else []

def firstChoice (T S : Tree) (hp : Priority T S) : List RawChoice → Option (Choice T S)
  | [] => none
  | s :: ss => if h : LocalGuard T S s then some ⟨s,hp,h⟩ else firstChoice T S hp ss

def select (T S : Tree) : Option (Choice T S) :=
  if hp : Priority T S then firstChoice T S hp (rawChoices T S) else none

/-- Executable selection binds directly to the proved universal original cover. -/
theorem selected_cover {T S : Tree} (s : Choice T S) {F : List (List Nat)}
    (hF : agreement T S F = true) :
    ∃ G, agreement T S G = true ∧ G.length ≤ F.length ∧
      (VertexGeometry.Refines G (literalThree S s.raw.cHead s.raw.xHead) ∨
       VertexGeometry.Refines G (isolatePartition S s.raw.a) ∨
       VertexGeometry.Refines G (pendantPartition T s.raw.a s.raw.c)) := by
  exact actual_rule4_cover s.priority.1 s.priority.2.1 s.admission.2.2.1
    (orderedCherries_sound s.admission.1) (orderedCherries_sound s.admission.2.1)
    s.admission.2.2.2.1 s.admission.2.2.2.2 hF

theorem firstChoice_complete {T S : Tree} (hp : Priority T S) (ss : List RawChoice)
    (s : RawChoice) (hm : s ∈ ss) (hs : LocalGuard T S s) :
    ∃ c, firstChoice T S hp ss = some c := by
  induction ss with
  | nil => simp at hm
  | cons x xs ih =>
    by_cases hx : LocalGuard T S x
    · exact ⟨⟨x,hp,hx⟩,by simp [firstChoice,hx]⟩
    · have hm' : s ∈ xs := by
        rcases List.mem_cons.1 hm with rfl | hh
        · exact False.elim (hx hs)
        · exact hh
      obtain ⟨c,hc⟩ := ih hm'
      exact ⟨c,by simp [firstChoice,hx,hc]⟩

/-- Every source Rule4 local guard is actually enumerated, regardless of child
orientation or the original DFS order of c and X2 pendant heads. -/
theorem rawChoices_complete {T S : Tree} (s : RawChoice) (hs : LocalGuard T S s) :
    s ∈ rawChoices T S := by
  unfold rawChoices
  apply List.mem_flatMap.2
  refine ⟨(s.a,s.b),hs.1,?_⟩
  apply List.mem_flatMap.2
  refine ⟨(s.a,s.c),hs.2.1,?_⟩
  have hl := two_cut_length hs.2.2.2.1
  simp only [Prod.fst,Prod.snd,hl,true_and,↓reduceIte]
  apply List.mem_flatMap.2
  refine ⟨s.cHead,two_cut_mem_left hs.2.2.2.1,?_⟩
  apply List.mem_map.2
  exact ⟨s.xHead,two_cut_mem_right hs.2.2.2.1,by cases s; rfl⟩

theorem select_complete {T S : Tree} (hp : Priority T S) (s : RawChoice)
    (hs : LocalGuard T S s) : ∃ c, select T S = some c := by
  obtain ⟨c,hc⟩ := firstChoice_complete hp (rawChoices T S) s (rawChoices_complete s hs) hs
  exact ⟨c,by simp [select,hp,hc]⟩
end Universal233.Rule4
