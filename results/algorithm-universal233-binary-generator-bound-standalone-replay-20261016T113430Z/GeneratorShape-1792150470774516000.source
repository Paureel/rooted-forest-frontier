import ProducerCostsControls
namespace GenericForest.BinaryProducer.Generator
open BinaryProvider Universal233.WholeSourceWork
/-- Proof measure of represented cells; scalar bit widths are tracked separately. -/
def size : GTree→Nat
 | .leaf g=>1+g.labels.length+g.origin.length
 | .node p l r=>1+p.length+size l+size r
@[simp] theorem size_native (T : GTree) : size T=Universal233.CoreWork.footprint (gtreeValue T) := by
 induction T <;> simp_all [size,gtreeValue,groupValue,blockValue_length,Universal233.CoreWork.footprint]
theorem size_pos (T : GTree) : 1≤size T := by cases T <;> simp only [size] <;> omega
def Wide (W : Nat) : GTree→Prop
 | .leaf g=>BlockWidth W g.labels
 | .node _ l r=>Wide W l ∧ Wide W r

theorem normalize_size (T : GTree) : size (normalizeBits T).value≤size T := by
 simpa only [size_native,normalizeBits_value] using Universal233.CoreWork.normalize_footprint (gtreeValue T)
theorem erase_size (p : RMAF.Vertex) (T U : GTree) (h : (eraseBits p T).value=some U) : size U≤size T := by
 have e:=eraseBits_value p T
 simp only [h,Option.map_some] at e
 simpa only [size_native] using Universal233.CoreWork.erase_footprint _ _ _ e.symm

theorem normalize_wide (W : Nat) (T : GTree) (h : Wide W T) : Wide W (normalizeBits T).value := by
 induction T with
 | leaf g=>exact h
 | node p l r ihl ihr=>
  have a:=ihl h.1;have b:=ihr h.2
  cases hl : (normalizeBits l).value <;> cases hr : (normalizeBits r).value
  all_goals simp only [hl,hr,Wide] at a b
  all_goals simp only [normalizeBits,hl,hr]
  all_goals first | exact ⟨a,b⟩ | skip
  split
  · simp only [Wide,appendLabels_value];intro x hx;rcases List.mem_append.mp hx with hx|hx;exact a x hx;exact b x hx
  · exact ⟨a,b⟩

theorem erase_wide (W : Nat) (p : RMAF.Vertex) (T U : GTree) (h : Wide W T)
 (e : (eraseBits p T).value=some U) : Wide W U := by
 induction T generalizing U with
 | leaf g=>
  dsimp only [eraseBits] at e
  split at e
  · contradiction
  · cases e;exact h
 | node v l r ihl ihr=>
  dsimp only [eraseBits] at e
  split at e
  · contradiction
  · cases hl : (eraseBits p l).value <;> cases hr : (eraseBits p r).value <;> simp only [hl,hr] at e
    · contradiction
    · cases e;exact ihr _ h.2 hr
    · cases e;exact ihl _ h.1 hl
    · cases e;exact ⟨ihl _ h.1 hl,ihr _ h.2 hr⟩

theorem groups_length (T : GTree) : (groupsBits T).value.length≤size T := by
 have h:=Universal233.CoreWork.groups_length (gtreeValue T)
 have e:=congrArg List.length (groupsBits_value T)
 simp only [groupsValue,List.length_map] at e
 rw [←e] at h
 simpa only [←size_native] using h

theorem group_size (T : GTree) (g : Group) (h : g∈(groupsBits T).value) :
 1+g.labels.length+g.origin.length≤size T := by
 have mem : groupValue g∈Universal233.CoreProgram.groups (gtreeValue T) := by
  rw [←groupsBits_value];exact List.mem_map.mpr ⟨g,h,rfl⟩
 simpa only [groupValue,blockValue_length,←size_native] using Universal233.CoreWork.group_size _ _ mem

theorem groups_wide (W : Nat) (T : GTree) (h : Wide W T) : ∀g∈(groupsBits T).value,BlockWidth W g.labels := by
 induction T with
 | leaf a=>simpa only [groupsBits,List.mem_singleton,forall_eq,Wide] using h
 | node p l r ihl ihr=>
  simp only [groupsBits,appendSpine_value,List.mem_append]
  intro g hg;rcases hg with hg|hg
  · exact ihl h.1 g hg
  · exact ihr h.2 g hg

theorem filterColor_sub (c : Color) (gs : List Group) : ∀g∈(filterColor c gs).value,g∈gs := by
 induction gs with
 | nil=>simp [filterColor]
 | cons a gs ih=>
  simp only [filterColor];split
  · intro g hg;rcases List.mem_cons.mp hg with rfl|hg
    · simp
    · exact List.mem_cons_of_mem _ (ih g hg)
  · intro g hg;exact List.mem_cons_of_mem _ (ih g hg)

theorem findUnique_mem (gs more : List Group) (g : Group) (h : (findUnique gs more).value=some g) : g∈more := by
 induction more with
 | nil=>simp [findUnique] at h
 | cons a more ih=>
  dsimp only [findUnique] at h
  split at h
  · cases h;simp
  · exact List.mem_cons_of_mem _ (ih h)

theorem mixedBits_mem (T : GTree) (a b : Group) (h : (mixedBits T).value=some (a,b)) :
 a∈(groupsBits T).value ∧ b∈(groupsBits T).value := by
 induction T with
 | leaf g=>simp only [mixedBits] at h;contradiction
 | node p l r ihl ihr=>
  cases l with
  | leaf x=>
   cases r with
   | leaf y=>cases h;simp [groupsBits]
   | node q u v=>
    have hr : (mixedBits (.node q u v)).value=some (a,b):=by simpa only [mixedBits,Option.or] using h
    have z:=ihr hr
    simp only [groupsBits,appendSpine_value,List.mem_append] at z ⊢;exact ⟨Or.inr z.1,Or.inr z.2⟩
  | node q u v=>
   cases r with
   | leaf y=>
    have hl : (mixedBits (.node q u v)).value=some (a,b):=by simpa only [mixedBits,Option.or_none] using h
    have z:=ihl hl
    simp only [groupsBits,appendSpine_value,List.mem_append] at z ⊢;exact ⟨Or.inl z.1,Or.inl z.2⟩
   | node q' u' v'=>
    change ((mixedBits (.node q u v)).value.or (mixedBits (.node q' u' v')).value)=some (a,b) at h
    cases hl : (mixedBits (.node q u v)).value with
    | none=>
     simp only [hl,Option.or] at h
     have z:=ihr h
     simp only [groupsBits,appendSpine_value,List.mem_append] at z ⊢;exact ⟨Or.inr z.1,Or.inr z.2⟩
    | some ab=>
     simp only [hl,Option.or,Option.some.injEq] at h
     have z:=ihl (h ▸ hl)
     simp only [groupsBits,appendSpine_value,List.mem_append] at z ⊢;exact ⟨Or.inl z.1,Or.inl z.2⟩

theorem chooseBits_mem (T : GTree) :
 (∀g,(chooseBits T).value=.one g→g∈(groupsBits T).value) ∧
 (∀a b,(chooseBits T).value=.two a b→a∈(groupsBits T).value ∧ b∈(groupsBits T).value) := by
 dsimp only [chooseBits]
 cases hg : (groupsBits T).value with
 | nil=>constructor <;> intros <;> contradiction
 | cons first rest=>
  simp only
  cases ha : (allColors first.color (first::rest)).value with
  | true=>simp only [ite_true];constructor <;> intros <;> contradiction
  | false=>
   simp only [Bool.false_eq_true,ite_false]
   cases hu : (findUnique (first::rest) (first::rest)).value with
   | some g=>
    constructor
    · intro x hx;cases hx;exact findUnique_mem _ _ g hu
    · intro a b h;contradiction
   | none=>
    cases hm : (mixedBits T).value with
    | none=>constructor <;> intros <;> contradiction
    | some ab=>
     rcases ab with ⟨a,b⟩
     cases he : (colorEq a.color b.color).value with
     | true=>simp only [he,ite_true];constructor <;> intros <;> contradiction
     | false=>
      simp only [he,Bool.false_eq_true,ite_false]
      constructor
      · intros;contradiction
      · intro x y h;cases h;simpa only [hg] using mixedBits_mem T a b hm
end GenericForest.BinaryProducer.Generator
