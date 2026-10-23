/- Contacted prover: a selected clade avoids the other labels' rooted span. -/
import SourceCladeHullsV2
open RMAF ForestState Universal233 Universal233.HardParent
open IndependentGeometry IndependentOneExchange
namespace ContactedClade

def Absent (T : Tree) (A : List Nat) : Prop := ∀x∈leaves T,x∉A
noncomputable def Clean (A D : List Nat) (T : Tree) : Prop :=
 Tree.rec (fun x=>x∈A→x∉D)
  (fun l r cl cr=>(Absent r A ∧ cl) ∨ (Absent l A ∧ cr) ∨ Absent (.node l r) D) T

theorem clean_leaf (A D : List Nat) (x : Nat) : Clean A D (.leaf x) ↔ (x∈A→x∉D) := Iff.rfl
 theorem clean_node (A D : List Nat) (l r : Tree) :
 Clean A D (.node l r) ↔
 (Absent r A ∧ Clean A D l) ∨ (Absent l A ∧ Clean A D r) ∨ Absent (.node l r) D := Iff.rfl

theorem clean_absent_A (T : Tree) {A D : List Nat} (no : Absent T A) : Clean A D T := by
 induction T with
 | leaf x => exact fun hx=>False.elim (no x (by simp [leaves]) hx)
 | node l r il ir =>
  exact Or.inl ⟨fun x hx=>no x (List.mem_append_right _ hx),il (fun x hx=>no x (List.mem_append_left _ hx))⟩

theorem clean_absent_D (T : Tree) {A D : List Nat} (no : Absent T D) : Clean A D T := by
 cases T with
 | leaf x => exact fun _=>no x (by simp [leaves])
 | node l r => exact Or.inr (Or.inr no)

theorem clean_span_disjoint (T : Tree) {A D : List Nat} (clean : Clean A D T) :
 ∀v∈minimalVertices A T,v∉rootedSpan D T := by
 induction T with
 | leaf x =>
  have no := clean
  change (x∈A→x∉D) at no
  by_cases ax : x∈A
  · simp [minimalVertices,rootedSpan,ax,no ax]
  · simp [minimalVertices,ax]
 | node l r il ir =>
  rcases clean with ⟨ar,cl⟩|⟨al,cr⟩|noD
  · have empty : (rootedSpan A r).isEmpty=true := by rw [span_absent r A ar];rfl
    rw [minimal_node_left A l r empty]
    intro v hv hd
    obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
    exact il cl w hw (span_child D l r false w hd)
  · have empty : (rootedSpan A l).isEmpty=true := by rw [span_absent l A al];rfl
    rw [minimal_node_right A l r empty]
    intro v hv hd
    obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
    exact ir cr w hw (span_child D l r true w hd)
  · have zero := span_absent (.node l r) D noD
    simp [zero]

theorem clade_clean {S U : Tree} {p : Vertex} {A D : List Nat}
 (sub : CoreGraph.subtree S p=some U) (nd : (leaves S).Nodup)
 (inside : ∀x∈A,x∈leaves U) (outside : Absent U D) : Clean A D S := by
 induction p generalizing S with
 | nil =>
  have eq : S=U := by simpa [CoreGraph.subtree] using sub
  subst S
  exact clean_absent_D U outside
 | cons side rest ih =>
  cases S with
  | leaf y => simp [CoreGraph.subtree] at sub
  | node l r =>
   have ns := List.nodup_append.1 nd
   cases side
   · change CoreGraph.subtree l rest=some U at sub
     have ar : Absent r A := by
      intro x xr xa
      exact ns.2.2 x (subtree_leaves_own sub x (inside x xa)) x xr rfl
     exact Or.inl ⟨ar,ih sub ns.1⟩
   · change CoreGraph.subtree r rest=some U at sub
     have al : Absent l A := by
      intro x xl xa
      exact ns.2.2 x xl x (subtree_leaves_own sub x (inside x xa)) rfl
     exact Or.inr (Or.inl ⟨al,ih sub ns.2.1⟩)

theorem iso_labels {T U : Tree} (iso : RootedIso T U) : ∀x,x∈leaves T↔x∈leaves U := by
 induction iso with
 | leaf y => exact fun _=>Iff.rfl
 | straight hl hr il ir => intro x;simp only [leaves,List.mem_append,il x,ir x]
 | swapped hl hr il ir => intro x;simp only [leaves,List.mem_append,il x,ir x];exact or_comm

theorem iso_absent {T U : Tree} (iso : RootedIso T U) (A : List Nat) : Absent T A↔Absent U A := by
 constructor
 · intro no x hx;exact no x ((iso_labels iso x).2 hx)
 · intro no x hx;exact no x ((iso_labels iso x).1 hx)

theorem iso_clean {T U : Tree} (iso : RootedIso T U) (A D : List Nat) : Clean A D T↔Clean A D U := by
 induction iso with
 | leaf x => exact Iff.rfl
 | straight hl hr il ir =>
  rw [clean_node,clean_node,iso_absent hr A,iso_absent hl A,il,ir,iso_absent (.straight hl hr) D]
 | swapped hl hr il ir =>
  rw [clean_node,clean_node,iso_absent hr A,iso_absent hl A,il,ir,iso_absent (.swapped hl hr) D]
  constructor <;> intro h
  · rcases h with h|h|h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rcases h with h|h|h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
end ContactedClade
