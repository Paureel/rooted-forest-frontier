import Hard2WholeLedgerV3

namespace SourceHard2WholeV3
open RMAF Universal233 SourceForestV3
open SourceCouplingV2 (Mode enabled)

-- This is a mathematical occurrence map, not a runtime search or cache.
theorem recorded_positions {rec chrono : List Occurrence} (hp : chrono.Perm rec) :
    ∃ position : {o // o∈chrono}→Fin rec.length,
      Function.Injective position ∧ ∀ x,rec.get (position x)=x.val := by
  classical
  have existsPosition : ∀ x : {o // o∈chrono},∃ i : Fin rec.length,rec.get i=x.val := by
    intro x
    obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp (hp.mem_iff.mp x.property)
    exact ⟨⟨i,hi⟩,he⟩
  let position (x : {o // o∈chrono}) : Fin rec.length:=Classical.choose (existsPosition x)
  have position_eq (x : {o // o∈chrono}) : rec.get (position x)=x.val:=Classical.choose_spec (existsPosition x)
  refine ⟨position,?_,position_eq⟩
  intro x y he
  apply Subtype.ext
  have hx:=position_eq x
  rw [he] at hx
  exact hx.symm.trans (position_eq y)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}

theorem live_recorded_positions {rec chrono : List Occurrence}
    (hp : chrono.Perm rec) (hr : ∀ o∈rec,SlotRealizes OrdExec mode o.2) :
    ∃ position : {o // o∈chrono ∧ o.2.live=true}→Fin rec.length,
      Function.Injective position ∧ ∀ x,
        rec.get (position x)=x.val ∧ enabled mode x.val.2.query.2=true ∧
        ∃ a,OrdExec x.val.2.query.1.1 x.val.2.query.1.2 x.val.2.query.2 a ∧
          x.val.2.returned=a.map (fun fs=>(fs.length-1,fs)) := by
  obtain ⟨position,inj,position_eq⟩:=recorded_positions hp
  let embed : {o // o∈chrono ∧ o.2.live=true}→{o // o∈chrono}:=
    fun x=>⟨x.val,x.property.1⟩
  refine ⟨fun x=>position (embed x),?_,?_⟩
  · intro x y he
    have hx:=inj he
    apply Subtype.ext
    exact congrArg (fun z : {o // o∈chrono}=>z.val) hx
  · intro x
    refine ⟨position_eq (embed x),?_⟩
    rcases hr x.val (hp.mem_iff.mp x.property.1) with ⟨off,rest⟩|⟨on,active,execution⟩
    · rw [x.property.2] at off
      contradiction
    · exact ⟨active,execution⟩

theorem live_source_positions {rec chrono : List Occurrence} {qs : List Q}
    (hp : chrono.Perm rec) (hq : rec.map (fun o=>o.2.query)=qs)
    (hr : ∀ o∈rec,SlotRealizes OrdExec mode o.2) :
    ∃ position : {o // o∈chrono ∧ o.2.live=true}→Fin qs.length,
      Function.Injective position ∧ ∀ x,
        qs.get (position x)=x.val.2.query ∧ enabled mode x.val.2.query.2=true ∧
        ∃ a,OrdExec x.val.2.query.1.1 x.val.2.query.1.2 x.val.2.query.2 a ∧
          x.val.2.returned=a.map (fun fs=>(fs.length-1,fs)) := by
  obtain ⟨pos,inj,position_eq⟩:=live_recorded_positions hp hr
  subst qs
  let position (x : {o // o∈chrono ∧ o.2.live=true}) :
      Fin (rec.map (fun o=>o.2.query)).length:=⟨(pos x).val,by simp⟩
  refine ⟨position,?_,?_⟩
  · intro x y he
    apply inj
    apply Fin.ext
    exact congrArg (fun z : Fin (rec.map (fun o=>o.2.query)).length=>z.val) he
  · intro x
    have hx:=position_eq x
    refine ⟨?_,hx.2⟩
    have hm : (rec.map (fun o=>o.2.query)).get (position x)=(rec.get (pos x)).2.query := by
      simp only [List.get_eq_getElem,List.getElem_map,position]
    exact hm.trans (congrArg (fun o=>o.2.query) hx.1)

theorem recorded_sum {rec chrono : List Occurrence} (hp : chrono.Perm rec)
    (weight : SourceForestV3.S→Nat) :
    (chrono.map (fun o=>weight o.2)).sum=(rec.map (fun o=>weight o.2)).sum :=
  (hp.map _).sum_nat

theorem chronological_distinct {rec chrono : List Occurrence} (hp : chrono.Perm rec)
    (distinct : rec.Pairwise (fun a b=>a.1≠b.1)) :
    chrono.Pairwise (fun a b=>a.1≠b.1) :=
  hp.pairwise_iff (fun h=>Ne.symm h) |>.mpr distinct
end SourceHard2WholeV3
