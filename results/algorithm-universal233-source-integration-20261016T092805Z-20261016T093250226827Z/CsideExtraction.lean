import OrientedBside
namespace Universal233.Case322Extraction
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322
set_option maxRecDepth 15000

def cSideEdges (T : Tree) (b c : Nat) : List RMAF.Vertex :=
 (cuts T b c).filter fun q => (subtreeLabels T q.dropLast).contains c && !(subtreeLabels T q.dropLast).contains b

theorem cSideEdges_sound {T : Tree} {b c : Nat} {q : RMAF.Vertex}
 (h : q ∈ cSideEdges T b c) : q ∈ cuts T b c ∧ c ∈ subtreeLabels T q.dropLast ∧ b ∉ subtreeLabels T q.dropLast := by
 have hh := List.mem_filter.1 h
 have pp : (subtreeLabels T q.dropLast).contains c = true ∧ (subtreeLabels T q.dropLast).contains b = false := by
   simpa only [Bool.and_eq_true,Bool.not_eq_true'] using hh.2
 refine ⟨hh.1,List.contains_iff_mem.1 pp.1,?_⟩
 intro hb
 have bb := List.contains_iff_mem.2 hb
 rw [bb] at pp
 simp at pp

theorem distinct_cside_parents {T : Tree} {b c : Nat} {q r : RMAF.Vertex}
 (hn : (leaves T).Nodup) (hq : q ∈ cSideEdges T b c) (hr : r ∈ cSideEdges T b c) (ne : q ≠ r) :
 q.dropLast ≠ r.dropLast := by
 have qs := cSideEdges_sound hq
 have rs := cSideEdges_sound hr
 have qsp := (cuts_spec T b c q).1 qs.1
 have rsp := (cuts_spec T b c r).1 rs.1
 intro parents
 obtain ⟨v,lv,pv⟩ := (subtreeLabels_prefix T q.dropLast c).1 qs.2.1
 have cT := leafAt_label T v c lv
 have noQ : ¬q <+: v := by
   intro h
   exact source_label_outside_pendant qs.1 (Or.inr rfl) cT ((subtreeLabels_prefix T q c).2 ⟨v,lv,h⟩)
 have noR : ¬r <+: v := by
   intro h
   exact source_label_outside_pendant rs.1 (Or.inr rfl) cT ((subtreeLabels_prefix T r c).2 ⟨v,lv,h⟩)
 rcases List.eq_nil_or_concat q with eq | ⟨p,s,eq⟩
 · exact qsp.2.1 eq
 rcases List.eq_nil_or_concat r with er | ⟨p',t,er⟩
 · exact rsp.2.1 er
 have qe : q = p ++ [s] := by simpa only [List.concat_eq_append] using eq
 have re : r = p' ++ [t] := by simpa only [List.concat_eq_append] using er
 have pp : p = p' := by simpa [qe,re] using parents
 subst p'
 have st : s ≠ t := by intro e; subst t; exact ne (qe.trans re.symm)
 have pv' : p <+: v := by simpa [qe] using pv
 obtain ⟨tail,ev⟩ := pv'
 cases tail with
 | nil =>
   have ve : v = p := by simpa using ev.symm
   have lep : LeafAt T p c := ve ▸ lv
   have qp : q = p := leaf_valid_descendant lep qsp.1 (by rw [qe]; exact List.prefix_append _ _)
   have nn := congrArg List.length qp
   simp [qe] at nn
 | cons u us =>
   have eu : u = s ∨ u = t := by cases u <;> cases s <;> cases t <;> simp_all
   rcases eu with rfl | rfl
   · exact noQ ⟨us,by simpa [qe,List.append_assoc] using ev⟩
   · exact noR ⟨us,by simpa [re,List.append_assoc] using ev⟩

/-- The selected c-side parents are ordered by actual original prefixes.
This derives the lower target cluster required by the original exchange. -/
theorem cside_actual_lower_cluster {T U V : Tree} {b c : Nat} {q r : RMAF.Vertex}
 (hn : (leaves T).Nodup) (hq : q ∈ cSideEdges T b c) (hr : r ∈ cSideEdges T b c) (ne : q ≠ r)
 (qU : subtree T q = some U) (rV : subtree T r = some V) :
 (∃ W z, subtree T z = some W ∧ c ∈ leaves W ∧
   (∀ x, x ∈ leaves U → x ∈ leaves W) ∧ (∀ x, x ∈ leaves V → x ∉ leaves W)) ∨
 (∃ W z, subtree T z = some W ∧ c ∈ leaves W ∧
   (∀ x, x ∈ leaves V → x ∈ leaves W) ∧ (∀ x, x ∈ leaves U → x ∉ leaves W)) := by
 have qs := cSideEdges_sound hq
 have rs := cSideEdges_sound hr
 obtain ⟨u,lu,pu⟩ := (subtreeLabels_prefix T q.dropLast c).1 qs.2.1
 obtain ⟨v,lv,pv⟩ := (subtreeLabels_prefix T r.dropLast c).1 rs.2.1
 have uv := leaf_unique hn lu lv
 rw [uv] at pu
 have parentsNe := distinct_cside_parents hn hq hr ne
 have one : ∀ {i j : RMAF.Vertex} {A B : Tree}, i ∈ cSideEdges T b c → j ∈ cSideEdges T b c →
   i.dropLast ≠ j.dropLast → i.dropLast <+: j.dropLast →
   subtree T i = some A → subtree T j = some B →
   ∃ W z, subtree T z = some W ∧ c ∈ leaves W ∧
    (∀ x, x ∈ leaves B → x ∈ leaves W) ∧ (∀ x, x ∈ leaves A → x ∉ leaves W) := by
   intro i j A B hi hj pn ij iA jB
   have isp := (cuts_spec T b c i).1 (cSideEdges_sound hi).1
   have jsp := (cuts_spec T b c j).1 (cSideEdges_sound hj).1
   obtain ⟨W,upper⟩ := valid_ancestor jsp.1 (List.dropLast_prefix j)
   have cW : c ∈ leaves W := by
     have cc := (cSideEdges_sound hj).2.1
     rwa [source_subtree_labels upper] at cc
   have noIt : ¬i <+: j.dropLast := offpath_no_descendant isp.2.1 isp.2.2.1 isp.2.2.2 jsp.2.2.1
   refine ⟨W,j.dropLast,upper,cW,cut_labels_parent jB upper,?_⟩
   intro x xA xW
   obtain ⟨p,lp,ip⟩ := (subtreeLabels_prefix T i x).1 (by rwa [source_subtree_labels iA])
   obtain ⟨z,lz,jz⟩ := (subtreeLabels_prefix T j.dropLast x).1 (by rwa [source_subtree_labels upper])
   have eq := leaf_unique hn lp lz
   rw [eq] at ip
   rcases List.prefix_or_prefix_of_prefix ip jz with itt | jti
   · exact noIt itt
   · have lt : i.dropLast.length < j.dropLast.length := by
       have le := ij.length_le
       have neq : i.dropLast.length ≠ j.dropLast.length := fun eq => pn (ij.eq_of_length eq)
       omega
     have le := jti.length_le
     have leni : i.length = i.dropLast.length+1 := by
       cases i with
       | nil => exact False.elim (isp.2.1 rfl)
       | cons s is => simp [List.length_dropLast]
     have lens : i.length = j.dropLast.length := by omega
     have eqt : j.dropLast = i := jti.eq_of_length lens.symm
     exact noIt (eqt ▸ List.prefix_rfl)
 rcases List.prefix_or_prefix_of_prefix pu pv with qp | rp
 · exact Or.inr (one hq hr parentsNe qp qU rV)
 · exact Or.inl (one hr hq parentsNe.symm rp rV qU)
end Universal233.Case322Extraction
