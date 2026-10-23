import SourceGuards
namespace Universal233.Hard2Overlap
open RMAF VertexGeometry SourceCoverage CoreProgram Integration

theorem select_exhaustive {T S : Tree} {A B C : List Nat}
 (ht : (leaves T).Nodup) (hl : ∀x,x∈leaves S → x∈leaves T)
 (hp : partitionCheck (leaves S) [A,B,C]=true) :
 ∃out,select T A B C=some out ∧ Valid T A B C out := by
 cases hab : overlap T A B with
 | none =>
  have ab := overlap_none hab
  cases hbc : overlap T B C with
  | none =>
   have bc := overlap_none hbc
   cases hac : overlap T A C with
   | none =>
    exact ⟨.disjoint,by simp [select,hab,hbc,hac],three_clear ab (overlap_none hac) bc⟩
   | some v =>
    obtain ⟨out,hout,hvalid⟩ := isolated_valid .acb ht hl hp ⟨v,overlap_sound hac⟩ ab (clear_symm bc)
    exact ⟨out,by simpa [select,hab,hbc,hac] using hout,hvalid⟩
  | some w =>
   have bw := overlap_sound hbc
   cases hac : overlap T A C with
   | none =>
    obtain ⟨out,hout,hvalid⟩ := isolated_valid .bca ht hl hp ⟨w,bw⟩ (clear_symm ab) (clear_symm (overlap_none hac))
    exact ⟨out,by simpa [select,hab,hbc,hac] using hout,hvalid⟩
   | some v =>
    have av := overlap_sound hac
    refine ⟨chain T A B C .acb v w,by simp [select,hab,hbc,hac],?_⟩
    exact chain_valid .acb hp av.1 av.2 bw.2 bw.1 ab
 | some v =>
  have av := overlap_sound hab
  cases hbc : overlap T B C with
  | none =>
   have bc := overlap_none hbc
   cases hac : overlap T A C with
   | none =>
    obtain ⟨out,hout,hvalid⟩ := isolated_valid .abc ht hl hp ⟨v,av⟩ (overlap_none hac) bc
    exact ⟨out,by simpa [select,hab,hbc,hac] using hout,hvalid⟩
   | some w =>
    have aw := overlap_sound hac
    refine ⟨chain T A B C .bac v w,by simp [select,hab,hbc,hac],?_⟩
    exact chain_valid .bac hp av.2 av.1 aw.1 aw.2 bc
  | some w =>
   have bw := overlap_sound hbc
   cases hac : overlap T A C with
   | none =>
    refine ⟨chain T A B C .abc v w,by simp [select,hab,hbc,hac],?_⟩
    exact chain_valid .abc hp av.1 av.2 bw.1 bw.2 (overlap_none hac)
   | some u =>
    have au := overlap_sound hac
    obtain ⟨x,hx,xa,xb,xc⟩ := executable_clique_selector T A B C ⟨v,av⟩ ⟨w,bw⟩ ⟨u,au⟩
    refine ⟨.clique x,by simp [select,hab,hbc,hac,hx],?_,xa,xb,xc⟩
    exact PairAssembly.overlap_internal T A B x (Assembly.parent_partition_disjoint S A B C hp).1 xa xb

/-- Determinism transfers the exhaustive guard theorem to the actual return. -/
theorem select_sound {T S : Tree} {A B C : List Nat} {out : Result}
 (ht : (leaves T).Nodup) (hl : ∀x,x∈leaves S → x∈leaves T)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (selected : select T A B C=some out) : Valid T A B C out := by
 obtain ⟨out',hs,hv⟩ := select_exhaustive ht hl hp
 have eq : out'=out := Option.some.inj (hs.symm.trans selected)
 simpa [eq] using hv

theorem selected_parent_permutation (o : Order) (A B C : List Nat) :
 (parents o A B C).Perm [A,B,C] := parents_perm o A B C
end Universal233.Hard2Overlap
