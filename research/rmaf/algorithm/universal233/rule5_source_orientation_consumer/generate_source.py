#!/usr/bin/env python3
"""One-shot author adaptation of frozen displayed-orientation proofs.
This is development transport, not an independent proof or geometry replay.
"""
from pathlib import Path
D=Path(__file__).resolve().parent;R=D.parents[4];S=R/'results/algorithm-universal233-rule5-final-classification-replay-20261015T145040Z'
a=(S/'Rule5Case323.lean').read_text();b=(S/'Rule5Case321.lean').read_text()
a=a.replace('import Rule5Exchange','import FinalInterface').replace('namespace Universal233.Rule5Local','namespace Universal233.Rule5SourceOrientation').replace('end Universal233.Rule5Local','end Universal233.Rule5SourceOrientation')
a=a.replace('HardParent CherryBranching','HardParent CherryBranching Rule5Local Rule5FinalClassification')
# All source base occurrences share two independently quantified child sides.
a=a.replace('{v : RMAF.Vertex}', '{v : RMAF.Vertex} {s t : Bool}').replace('{v p : RMAF.Vertex}', '{v p : RMAF.Vertex} {s t z : Bool}')
a=a.replace('some (.node (.node (.leaf a) X) (.leaf c))','some (fork t (fork s (.leaf a) X) (.leaf c))')
a=a.replace('leaves (.node (.node (.leaf a) X) (.leaf c))','leaves (fork t (fork s (.leaf a) X) (.leaf c))')
a=a.replace('S _ v B hn atV','S _ v B hn atV')
a=a.replace('some (.node (.node (.leaf a) X) (.leaf c))','some (fork t (fork s (.leaf a) X) (.leaf c))')
a=a.replace('v ++ [false,true]','v ++ [t,!s]').replace('v ++ [true]','v ++ [!t]')
a=a.replace('rw [subtree_append he]; rfl','rw [subtree_append he]; exact fork_first t _ _') # fix per cases below
# Nested actual subtree labels need both fork directions.
a=a.replace('rw [subtree_append he]; exact fork_first t _ _\n   have hr', 'rw [subtree_append he]; simpa [subtree] using fork_second s (.leaf a) X\n   have hr')
a=a.replace('rw [subtree_append he]; exact fork_first t _ _\n have first', 'rw [subtree_append he]; exact fork_second t _ _\n have first')
a=a.replace('rw [subtree_append he]; exact fork_first t _ _\n   rw [splitTwo', 'rw [subtree_append he]; exact fork_second t _ _\n   rw [splitTwo')
a=a.replace('simp [leaves', 'simp [fork_mem,leaves')
# Replace source_base_proper with orientation-free nodup proof.
x=a.index('theorem source_base_proper');y=a.index('/-- Literal Figure15.3',x)
a=a[:x]+'''theorem source_base_proper {S X : Tree} {v : RMAF.Vertex} {s t : Bool} {a c : Nat}
 (hn : (leaves S).Nodup)
 (he : subtree S v = some (fork t (fork s (.leaf a) X) (.leaf c))) :
 a ∉ leaves X ∧ c ∉ leaves X ∧ a ≠ c := by
 have nd := (subtreeLabels_sublist S v).nodup hn
 rw [source_subtree_labels he] at nd
 have out := fork_nodup_parts nd
 have inner := fork_nodup_parts out.1
 refine ⟨?_,?_,?_⟩
 · exact inner.2.2 a (by simp [leaves])
 · intro h
   exact out.2.2 c ((fork_mem s _ _ _).2 (Or.inr h)) (by simp [leaves])
 · intro e
   exact out.2.2 a ((fork_mem s _ _ _).2 (Or.inl (by simp [leaves]))) (by simp [leaves,e])

'''+a[y:]
# Generic fork occupancy supports both literal child sides.
x=a.index('theorem original_fork_occupies');y=a.index('theorem singleton_excludes_other',x)
a=a[:x]+'''theorem original_fork_occupies {T L R : Tree} {q : RMAF.Vertex} {s : Bool}
 {B : List Nat} {x y : Nat} (he : subtree T q = some (fork s L R))
 (hx : x ∈ leaves L) (hy : y ∈ leaves R) (xB : x ∈ B) (yB : y ∈ B) :
 q ∈ minimalVertices B T := by
 cases s
 · exact Rule5Local.original_fork_occupies he hx hy xB yB
 · exact Rule5Local.original_fork_occupies he hy hx yB xB

'''+a[y:]
# Target root genericization in third-case lemmas only.
a=a.replace('{S X U : Tree} {v : RMAF.Vertex} {s t : Bool}', '{S X U : Tree} {v : RMAF.Vertex} {s t z : Bool}')
a=a.replace('(.node (.leaf c) U)', '(fork z U (.leaf c))')
a=a.replace('have xU : x ∈ leaves U := by simpa [leaves,xnc] using xT','have xU : x ∈ leaves U := ((fork_mem z U (.leaf c) x).1 xT).resolve_right (by simpa [leaves] using xnc)')
a=a.replace('have dU : d ∈ leaves U := by simpa [leaves,dc] using dT','have dU : d ∈ leaves U := ((fork_mem z U (.leaf c) d).1 dT).resolve_right (by simpa [leaves] using dc)')
a=a.replace('have ht : (c :: leaves U).Nodup := by simpa [leaves] using hnT\n   exact (List.nodup_cons.1 ht).1','intro h; exact (fork_nodup_parts hnT).2.2 c h (by simp [leaves])')
a=a.replace('(q:=[true]) rfl he','(q:=[z]) (fork_first z U (.leaf c)) he')
# All source root subtree references may still use literal nodes in atV values.
a=a.replace('(.node (.node (.leaf a) X) (.leaf c))','(fork t (fork s (.leaf a) X) (.leaf c))')
# Prefix source321 module in the same fresh namespace.
b=b.replace('import Rule5Case323','import SourceTransport323').replace('namespace Universal233.Rule5Local','namespace Universal233.Rule5SourceOrientation').replace('end Universal233.Rule5Local','end Universal233.Rule5SourceOrientation')
b=b.replace('HardParent CherryBranching','HardParent CherryBranching Rule5Local Rule5FinalClassification')
b=b.replace('{q : RMAF.Vertex}\n {F', '{q : RMAF.Vertex} {s : Bool}\n {F')
b=b.replace('some (.node (.leaf a) X)','some (fork s (.leaf a) X)').replace('leaves (.node (.leaf a) X)','leaves (fork s (.leaf a) X)')
b=b.replace('q ++ [false]', 'q ++ [s]')
b=b.replace('rw [LeafAt,subtree_append he]; rfl','rw [LeafAt,subtree_append he]; exact fork_first s _ _')
b=b.replace('{v w : RMAF.Vertex}', '{v w : RMAF.Vertex} {s t : Bool}').replace('{v w p : RMAF.Vertex}', '{v w p : RMAF.Vertex} {s t : Bool}')
b=b.replace('(.node (.node (.leaf a) X) (.leaf c))','(fork t (fork s (.leaf a) X) (.leaf c))')
b=b.replace('v ++ [false,true]','v ++ [t,!s]').replace('v ++ [false]','v ++ [t]').replace('v ++ [true]','v ++ [!t]')
b=b.replace('rw [subtree_append he]; rfl','rw [subtree_append he]; exact fork_first t _ _',1)
b=b.replace('rw [subtree_append he]; rfl','rw [subtree_append he]; simpa [subtree] using fork_second s (.leaf a) X',1)
b=b.replace('rw [subtree_append he]; rfl','rw [subtree_append he]; exact fork_second t _ _',1)
b=b.replace('some (.node (.leaf a) X)','some (fork s (.leaf a) X)')
b=b.replace('rw [subtree_append he]; rfl','rw [subtree_append he]; simpa [subtree] using fork_second s (.leaf a) X',1)
b=b.replace('rw [subtree_append he]; rfl','rw [subtree_append he]; exact fork_second t _ _',1)
b=b.replace('simp [leaves','simp [fork_mem,leaves')
(D/'SourceTransport323.lean').write_text(a);(D/'SourceTransport321.lean').write_text(b)
