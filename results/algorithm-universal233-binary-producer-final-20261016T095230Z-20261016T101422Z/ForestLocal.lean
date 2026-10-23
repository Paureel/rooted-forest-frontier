import ForestQueries
import Indexing
namespace GenericForest
open RMAF RestrictionBridge ForestState OutputState ForestGroups VertexGeometry
open Universal233 Universal233.PaidQueries Universal233.MafScheduler

def pair (t s : Tree) : Tree × Tree := ((restrict (leaves s) t).getD t,s)

theorem pair_actual (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (s : Tree) (hs : s ∈ ss) :
    componentPair t s = some (pair t s) ∧ restrict (leaves s) t = some (pair t s).1 ∧
      DepthOne.proper (pair t s).1 (pair t s).2 = true := by
  obtain ⟨u,hp',hu,hl,hproper⟩ := component_pair_proper t ss hp s hs
  simpa [pair,hu] using And.intro hp' (And.intro hu hproper)

theorem filter_single {α : Type} (L : List α) (p : α → Bool) (s : α)
    (nd : L.Nodup) (hs : s ∈ L) (hc : ∀ r ∈ L, p r = true ↔ r = s) : L.filter p = [s] := by
  induction L with
  | nil => simp at hs
  | cons a L ih =>
    have hn := List.nodup_cons.1 nd
    by_cases he : a = s
    · subst a
      have hp := (hc s (by simp)).2 rfl
      have hz : L.filter p = [] := List.filter_eq_nil_iff.2 (by
        intro r hr hpr
        have he := (hc r (by simp [hr])).1 hpr
        exact hn.1 (he ▸ hr))
      simp [hp,hz]
    · have hsL : s ∈ L := (List.mem_cons.1 hs).resolve_left (Ne.symm he)
      have hp : p a = false := by
        cases hpa : p a
        · rfl
        · exact False.elim (he ((hc a (by simp)).1 hpa))
      simpa [hp] using ih hn.2 hsL (fun r hr => hc r (by simp [hr]))

theorem owned_single (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (s : Tree) (hs : s ∈ ss) : owned ss (leaves s) = [s] := by
  apply filter_single ss _ s (proper_sources_nodup t ss hp) hs
  intro r hr
  rw [contained_iff]
  constructor
  · intro sub
    obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil (leaves r) (RestrictionBridge.leaves_nonempty r)
    exact source_owner t ss hp r s hr hs x hx (sub hx)
  · intro he; subst r; exact List.Subset.refl _

theorem local_pair_state (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (s : Tree) (hs : s ∈ ss) : proper (some (pair t s).1) [s] = true := by
  have hQ := (proper_parts _ _ hp).2
  have own : Owns ss (ss.map leaves) := fun r hr => ⟨leaves r,List.mem_map.2 ⟨r,hr,rfl⟩,List.Subset.refl _⟩
  have hh := local_proper (some t) ss (ss.map leaves) hp hQ own (leaves s) (List.mem_map.2 ⟨s,hs,rfl⟩)
  simpa [localTarget,(pair_actual t ss hp s hs).2.1,owned_single t ss hp s hs] using hh

theorem local_pair_forward (t : Tree) (ss : List Tree) (G : Forest)
    (ha : agrees (some t) ss G = true) (s : Tree) (hs : s ∈ ss) :
    agreement (pair t s).1 (pair t s).2 (family (leaves s) G) = true := by
  have hp := (agrees_parts _ _ _ ha).1
  have own : Owns ss (ss.map leaves) := fun r hr => ⟨leaves r,List.mem_map.2 ⟨r,hr,rfl⟩,List.Subset.refl _⟩
  have hh := local_forward (some t) ss (ss.map leaves) G ha (proper_parts _ _ hp).2 own
    (leaves s) (List.mem_map.2 ⟨s,hs,rfl⟩)
  have hh' : agrees (some (pair t s).1) [s] (family (leaves s) G) = true := by
    simpa [localTarget,(pair_actual t ss hp s hs).2.1,owned_single t ss hp s hs] using hh
  exact (initial_state_agreement_iff _ s _ (local_pair_state t ss hp s hs)).1 hh'

theorem local_assemble (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (clear : pairwiseEmbeddings t (ss.map leaves) = true) (out : Tree → Forest)
    (ha : ∀ s ∈ ss, agreement (pair t s).1 (pair t s).2 (out s) = true) :
    agrees (some t) ss (ss.flatMap out) = true ∧
      additionalCost ss (ss.flatMap out) = (ss.map (fun s => (out s).length-1)).sum := by
  classical
  let owner : List Nat → Tree := fun U => if h : ∃ s ∈ ss, leaves s = U then h.choose else .leaf 0
  have owner_spec (U : List Nat) (hU : U ∈ ss.map leaves) : owner U ∈ ss ∧ leaves (owner U) = U := by
    have hx : ∃ s ∈ ss, leaves s = U := List.mem_map.1 hU
    simpa only [owner,dite_eq_left hx] using hx.choose_spec
  have owner_source (s : Tree) (hs : s ∈ ss) : owner (leaves s) = s := by
    have h := owner_spec (leaves s) (List.mem_map.2 ⟨s,hs,rfl⟩)
    obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil (leaves s) (RestrictionBridge.leaves_nonempty s)
    exact source_owner t ss hp _ s h.1 hs x (by simpa [h.2] using hx) hx
  let H : List Nat → Forest := fun U => out (owner U)
  have hQ := (proper_parts _ _ hp).2
  have own : Owns ss (ss.map leaves) := fun s hs => ⟨leaves s,List.mem_map.2 ⟨s,hs,rfl⟩,List.Subset.refl _⟩
  have cross : CrossClear (some t) ss (ss.map leaves) := by
    intro u hu U hU V hV hne a ha b hb v hv hw
    have hut : u = t := Option.some.inj hu.symm
    subst u
    have hA := (mem_owned _ _ _).1 ha
    have hB := (mem_owned _ _ _).1 hb
    exact pairwise_distinct t _ clear U V hU hV hne v
      (VertexGeometry.executable_span_monotone t _ U hA.2 v hv)
      (VertexGeometry.executable_span_monotone t _ V hB.2 v hw)
  have localValid (U : List Nat) (hU : U ∈ ss.map leaves) :
      agrees (localTarget (some t) U) (owned ss U) (H U) = true := by
    obtain ⟨s,hs,rfl⟩ := List.mem_map.1 hU
    have hloc := (initial_state_agreement_iff _ s _ (local_pair_state t ss hp s hs)).2 (ha s hs)
    simpa only [localTarget,Option.bind_some,(pair_actual t ss hp s hs).2.1,
      owned_single t ss hp s hs,H,owner_source s hs] using hloc
  have he : (ss.map leaves).flatMap H = ss.flatMap out := by
    rw [List.flatMap_map]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro s hs
    simp only [Function.comp_def,H,owner_source s hs]
  have hstate := reverse_reconstruction (some t) ss (ss.map leaves) H hp hQ own cross localValid
  have hcost := reverse_exact_cost (some t) ss (ss.map leaves) H hp hQ own localValid
  have hsum : ((ss.map leaves).map (fun U => additionalCost (owned ss U) (H U))).sum =
      (ss.map (fun s => (out s).length-1)).sum := by
    simp only [List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro s hs
    simp [owned_single t ss hp s hs,H,owner_source s hs,additionalCost]
  rw [hsum,he] at hcost
  exact ⟨by simpa only [he] using hstate,hcost.symm⟩

end GenericForest
