import ValidPartition

/-! Exact hand-specified positive/negative fixtures, frozen in SPEC before the
proof run. These exercise production history plus original leaf-region queries;
they are author development controls, not independent verification. -/
namespace Universal233.CutRealization.Controls
open RMAF CoreGraph CoreProgram Integration List

def regionCheck (cuts : List RMAF.Vertex) (r v : RMAF.Vertex) : Bool :=
  decide (Pre r v) && cuts.all (fun p => decide (Pre p v → Pre p r))

theorem regionCheck_correct (cuts : List RMAF.Vertex) (r v : RMAF.Vertex) :
    regionCheck cuts r v = true ↔ Region cuts r v := by
  simp only [regionCheck,Region,List.all_eq_true,Bool.and_eq_true,decide_eq_true_eq]

def leafPairs : Tree → List (RMAF.Vertex × Nat)
  | .leaf x => [([],x)]
  | .node l r => (leafPairs l).map (fun z => (false :: z.1,z.2)) ++
      (leafPairs r).map (fun z => (true :: z.1,z.2))

theorem leafPairs_correct (T : Tree) (v : RMAF.Vertex) (x : Nat) :
    (v,x) ∈ leafPairs T ↔ LeafAt T v x := by
  induction T generalizing v with
  | leaf y => cases v <;> simp [leafPairs,LeafAt,subtree,eq_comm]
  | node l r ihl ihr =>
    cases v with
    | nil => simp [leafPairs,LeafAt,subtree]
    | cons b v => cases b <;> simpa [leafPairs,LeafAt,subtree,Prod.mk.injEq] using (by
        first | exact ihl v | exact ihr v)

def leafLabels (T : Tree) (cuts : List RMAF.Vertex) (r : RMAF.Vertex) : List Nat :=
  ((leafPairs T).filter (fun z => regionCheck cuts r z.1)).map Prod.snd

theorem leafLabels_correct (T : Tree) (cuts : List RMAF.Vertex) (r : RMAF.Vertex) (x : Nat) :
    x ∈ leafLabels T cuts r ↔ ∃ v, LeafAt T v x ∧ Region cuts r v := by
  simp only [leafLabels,List.mem_map,List.mem_filter]
  constructor
  · rintro ⟨⟨v,y⟩,⟨hm,hr⟩,he⟩
    simp only at he
    subst y
    exact ⟨v,(leafPairs_correct T v x).1 hm,(regionCheck_correct cuts r v).1 hr⟩
  · rintro ⟨v,hv,hr⟩
    exact ⟨(v,x),⟨(leafPairs_correct T v x).2 hv,(regionCheck_correct cuts r v).2 hr⟩,rfl⟩

def rootTree : Tree := .node (.leaf 4) (.leaf 5)
def rootOutput : Output := ⟨[[4],[5]],[[false]]⟩

theorem singleton_output : (generate (.leaf 7) id 0).outputs = [⟨[[7]],[]⟩] := by decide

theorem root_suppression_output : (generate rootTree id 1).outputs = [rootOutput] := by decide

theorem root_suppression_realized : RealizedOutput rootTree rootOutput :=
  generate_original_realization rootTree id 1 rootOutput (by rw [root_suppression_output]; simp)

theorem root_vertex_retained_live : regionCheck [[false]] [] [] = true := by decide

theorem root_live_leaf : leafLabels rootTree [[false]] [] = [5] := by decide

/-- Cutting q first removes only label 0. The two surviving same-color groups
below p then coarsen to a group at p, excluding the earlier detached descendant. -/
def nested : Tree := .node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 3)
def nestedColor (x : Nat) : Nat := if x = 0 then 1 else if x = 3 then 2 else 0
def q : RMAF.Vertex := [false,false,false]
def p : RMAF.Vertex := [false]
def firstGroup : Group := ⟨q,[0],1⟩
def mergedGroup : Group := ⟨p,[1,2],0⟩
def state1 : GTree := .node []
  (.node [false] (.leaf ⟨[false,false,true],[1],0⟩) (.leaf ⟨[false,true],[2],0⟩))
  (.leaf ⟨[true],[3],2⟩)
def state2 : GTree := .leaf ⟨[true],[3],2⟩
def nestedOutput : Output := ⟨[[1,2],[0],[3]],[p,q]⟩

theorem nested_nodup : (leaves nested).Nodup := by decide

theorem first_history : History nested nestedColor state1 [firstGroup] [q] := by
  exact History.detached (History.normalized History.initial)
    (v := [false,false,false]) (g := firstGroup) (by rfl) (by decide) (by decide)
    (by simp) (by decide)

theorem coarsened_group_reachable :
    GroupLeafAt (normalize state1) [false] mergedGroup := by rfl

theorem nested_continuation :
    ComponentLabels nested [p,q] p [1,2] ∧ ComponentLabels nested [p,q] [] [3] ∧
    (∀ r, r ∈ [q] → ∀ a, ResidualWalk nested [p,q] r a ↔ ResidualWalk nested [q] r a) ∧
    ¬ ResidualWalk nested [p,q] [] p := by
  exact History.continuation_components (next := state2) (History.normalized first_history) nested_nodup
    coarsened_group_reachable (by decide) (by decide) (by decide) (by decide)

theorem nested_output : (generate nested nestedColor 2).outputs = [nestedOutput] := by decide

theorem nested_realized : RealizedOutput nested nestedOutput :=
  generate_original_realization nested nestedColor 2 nestedOutput (by rw [nested_output]; simp)

theorem nested_old_descendant_stays_detached : leafLabels nested [p,q] q = [0] := by decide

theorem nested_new_group_excludes_descendant : leafLabels nested [p,q] p = [1,2] := by decide

theorem suppressed_original_path_retained : regionCheck [q] [] [false,false] = true := by decide

theorem leafless_corruption_is_visible : leafLabels rootTree [[false],[true]] [] = [] := by decide

theorem nested_checked_source_core :
    ∃ o, o ∈ (generate nested nestedColor 2).outputs ∧
      partitionCheck (leaves nested) o.partition = true ∧
      VertexGeometry.Refines [[0],[1,2],[3]] o.partition ∧ RealizedOutput nested o ∧
      (∀ b, b ∈ o.partition → VertexGeometry.LabelMonochromatic nestedColor b) ∧
      colorCount nested nestedColor - 1 ≤ o.sourceCuts.length ∧ o.sourceCuts.length ≤ 2 := by
  apply checked_source_core nested [[0],[1,2],[3]] nestedColor nested_nodup (by decide) (by decide)
  intro b hb x y hx hy
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl <;> simp_all [nestedColor]
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

end Universal233.CutRealization.Controls
