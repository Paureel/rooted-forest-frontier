import LocalSplit

/-! Exact finite degree in the unchanged, unsuppressed extractor support. -/
namespace DegreeTwo
open RMAF BridgeReview DegreeTwoGraph

def edgeBool (v w : Vertex) : Bool :=
  w == v ++ [false] || w == v ++ [true] ||
  v == w ++ [false] || v == w ++ [true]

theorem edgeBool_iff (v w : Vertex) : edgeBool v w = true ↔ Adj v w := by
  simp only [edgeBool, Bool.or_eq_true, beq_iff_eq, Adj]
  constructor
  · rintro (((h | h) | h) | h)
    · exact Or.inl ⟨false,h⟩
    · exact Or.inl ⟨true,h⟩
    · exact Or.inr ⟨false,h⟩
    · exact Or.inr ⟨true,h⟩
  · rintro (⟨b,h⟩ | ⟨b,h⟩) <;> cases b <;> simp_all

theorem eraseDups_nodup (s : List Vertex) : s.eraseDups.Nodup := by
  cases s with
  | nil => simp
  | cons a s =>
    rw [List.eraseDups_cons, List.nodup_cons]
    exact ⟨by simp, eraseDups_nodup (s.filter (fun b => !b == a))⟩
termination_by s.length
decreasing_by
  have h := List.length_filter_le (fun b => !b == a) s
  simp only [List.length_cons]
  omega

def supportNeighbors (s : List Vertex) (v : Vertex) : List Vertex :=
  s.eraseDups.filter (edgeBool v)

theorem supportNeighbors_mem (s : List Vertex) (v w : Vertex) :
    w ∈ supportNeighbors s v ↔ w ∈ s ∧ Adj v w := by
  simp [supportNeighbors, edgeBool_iff]

theorem supportNeighbors_nodup (s : List Vertex) (v : Vertex) :
    (supportNeighbors s v).Nodup := (eraseDups_nodup s).filter _

theorem supportNeighbors_length_two_iff (s : List Vertex) (v : Vertex) :
    (supportNeighbors s v).length = 2 ↔ ExactTwo (fun w => w ∈ s) v := by
  constructor
  · intro h
    have he := List.eq_getElem_of_length_eq_two (supportNeighbors s v) h
    generalize ha : (supportNeighbors s v)[0]'(by omega) = a at he
    generalize hb : (supportNeighbors s v)[1]'(by omega) = b at he
    have hn := supportNeighbors_nodup s v
    rw [he] at hn
    have hab : a ≠ b := by simpa using hn
    have hma : a ∈ supportNeighbors s v := by simp [he]
    have hmb : b ∈ supportNeighbors s v := by simp [he]
    obtain ⟨hsa,hea⟩ := (supportNeighbors_mem s v a).mp hma
    obtain ⟨hsb,heb⟩ := (supportNeighbors_mem s v b).mp hmb
    refine ⟨a,b,hab,hsa,hea,hsb,heb,?_⟩
    intro w hw hew
    have hm := (supportNeighbors_mem s v w).mpr ⟨hw,hew⟩
    simpa [he] using hm
  · rintro ⟨a,b,hab,hsa,hea,hsb,heb,hall⟩
    have hsub : supportNeighbors s v ⊆ [a,b] := by
      intro w hw
      obtain ⟨hsw,hew⟩ := (supportNeighbors_mem s v w).mp hw
      simpa using hall w hsw hew
    have hsub' : [a,b] ⊆ supportNeighbors s v := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact (supportNeighbors_mem s v _).mpr ⟨hsa,hea⟩
      · exact (supportNeighbors_mem s v _).mpr ⟨hsb,heb⟩
    have hn : [a,b].Nodup := by simp [hab]
    have hle := (supportNeighbors_nodup s v).length_le_of_subset hsub
    have hge := hn.length_le_of_subset hsub'
    simp only [List.length_cons, List.length_nil] at hle hge
    omega

def supportDegree (s : List Vertex) (v : Vertex) : Nat :=
  if s.contains v then (supportNeighbors s v).length else 0

theorem supportDegree_two_iff (s : List Vertex) (v : Vertex) :
    supportDegree s v = 2 ↔ v ∈ s ∧ ExactTwo (fun w => w ∈ s) v := by
  by_cases hv : v ∈ s
  · simp [supportDegree, hv, supportNeighbors_length_two_iff]
  · simp [supportDegree, hv]

def actualDegree (t : Tree) (B : List Nat) (v : Vertex) : Nat :=
  supportDegree (minimalVertices B t) v

theorem actualDegree_two_iff (t : Tree) (B : List Nat) (v : Vertex) :
    actualDegree t B v = 2 ↔ v ∈ minimalVertices B t ∧
      ExactTwo (fun w => w ∈ minimalVertices B t) v :=
  supportDegree_two_iff _ _

theorem actualDegree_propagation (B S : List Nat) (t : Tree) (v : Vertex)
    (hsub : ∀ x, x ∈ B → x ∈ S)
    (hv : v ∈ minimalVertices B t) (hnt : v ∉ LeastEmbedding.terminals B t)
    (hdegree : actualDegree t S v = 2) : actualDegree t B v = 2 := by
  exact (actualDegree_two_iff t B v).mpr ⟨hv,
    actual_degree_propagation B S t v hsub hv hnt
      ((actualDegree_two_iff t S v).mp hdegree).2⟩

end DegreeTwo
