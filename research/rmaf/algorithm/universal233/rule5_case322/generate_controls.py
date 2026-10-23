#!/usr/bin/env python3
"""One-shot author controls from pre-pinned literal trees, no new search."""
from pathlib import Path
import controls
D=Path(__file__).resolve().parent
ids=dict(a=0,b=1,c=2,w=3,t=4,x=5,p=6,q=7,y=8,z=9)
def ts(t):return f'.leaf {ids[t]}' if isinstance(t,str) else f'(.node ({ts(t[0])}) ({ts(t[1])}))'
def vs(s):return '['+','.join('true' if x=='1' else 'false' for x in s)+']'
def fs(F):return '['+','.join('['+','.join(str(ids[x]) for x in B)+']' for B in F)+']'
txt='import Case322Caller\nnamespace Universal233.Rule5Case322.Controls\nopen RMAF Universal233.Rule5Case322 Universal233.Rule5Local\nopen Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching\nset_option maxRecDepth 20000\n'
for name,(t,u,cost) in controls.fixtures().items():
 txt+=f'def {name}T : Tree := {ts(t)}\ndef {name}S : Tree := {ts(u)}\n'
 txt+=f'theorem {name}_admitted : admitted {name}T {name}S 0 1 = true := by decide\n'
 qa=controls.L.singleton_arc(t,'a');qs=controls.L.branches(t,u,controls.L.classify(t,u))[2]['cuts'][1:]
 txt+=f'def {name}qa : RMAF.Vertex := {vs(qa)}\ndef {name}qs : List RMAF.Vertex := ['+','.join(vs(q) for q in qs)+']\n'
 txt+=f'theorem {name}_current_guards : (typeIIBranches {name}T {name}S 0 1 {name}qa [true] {name}qs).all (currentGuard {name}T {name}S) = true := by decide\n'
 txt+=f'theorem {name}_raw_costs : (typeIIBranches {name}T {name}S 0 1 {name}qa [true] {name}qs).map paid = [2,1,{len(qs)+1}] := by decide\n'
# two selected alternatives for actual I list
(t,u,_)=controls.fixtures()['i'];C=controls.L.classify(t,u);B=controls.L.branches(t,u,C)
q,r=B[2]['cuts'][1],B[3]['cuts'][1]
txt+=f'theorem i_all_current_guards : (typeIBranches iT iS 0 1 iqa [true] {vs(q)} {vs(r)}).all (currentGuard iT iS) = true := by decide\n'
txt+=f'theorem i_all_raw_costs : (typeIBranches iT iS 0 1 iqa [true] {vs(q)} {vs(r)}).map paid = [2,1,2,2] := by decide\n'
F=[['a'],['b','c','w'],['t'],['x'],['p'],['q']]
txt+=f'def wrongSavingF : List (List Nat) := {fs(F)}\n'
txt+='theorem wrongSaving_valid : agreement iT iS wrongSavingF = true := by decide\n'
txt+='theorem wrongSaving_a_single : [0] ∈ wrongSavingF := by decide\n'
txt+='theorem wrongSaving_b_nonsingle : [1] ∉ wrongSavingF := by decide\n'
txt+='theorem wrongSaving_extra2 : (splitTwo wrongSavingF iS [false,false,true] [false,true]).length = wrongSavingF.length+2 := by decide\n'
txt+='end Universal233.Rule5Case322.Controls\n';(D/'Case322Controls.lean').write_text(txt)
(D/'Case322False.lean').write_text('import Case322Controls\nopen RMAF Universal233.Rule5Case322 Universal233.Rule5Case322.Controls Universal233.Rule5Local\nexample : (splitTwo wrongSavingF iS [false,false,true] [false,true]).length ≤ wrongSavingF.length+1 := by decide\nexample : (typeIIBranches iiT iiS 0 1 iiqa [true] iiqs).map paid = [2,1,2] := by decide\n')
