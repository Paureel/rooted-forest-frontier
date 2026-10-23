#!/usr/bin/env python3
"""Frozen false-control observers: correctness-only Fprime, local charge and literal multiplicity."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;R=P.parent/'sol-preparation-READY-v1/preparation';d=json.loads((R/'fixtures-v1.json').read_text());pub=d['reused_public_false_control'];g=d['fixtures'][0]
def tree(t):return '.leaf '+str(t)if isinstance(t,int)else '(.node ('+tree(t[0])+') ('+tree(t[1])+'))'
def ls(x):return '['+','.join(ls(y)if isinstance(y,list)else str(y)for y in x)+']'
s='''import IndependentReadout
open Lean Universal233 RMAF CoreProgram Universal233.BinaryCheap Universal233.RankDichotomy
namespace IndependentSeparation
'''
for n,t in [('ps',pub['S']),('pt',pub['T']),('s',g['S']),('t',g['T'])]:s+='def '+n+' : Tree := '+tree(t)+'\n'
s+='def F0 : List (List Nat) := '+ls(d['public_F'])+'\ndef Fprime : List (List Nat) := '+ls(d['public_Fprime'])+'\n'
s+='def A : List Nat := '+ls(g['P'][0])+'\ndef B : List Nat := '+ls(g['P'][1])+'\ndef C : List Nat := '+ls(g['P'][2])+'\n'
s+='def D := PairGeometry.descendants t [false,false]\n'
s+='def out := (generate s (cheapColor A B D) 3).outputs\n'
s+='def pubout := (generate ps (cheapColor '+ls(pub['P'][1])+' '+ls(pub['P'][0])+' (PairGeometry.descendants pt [false,false])) 6).outputs\n'
s+='''#eval IndependentReadout.emit (Json.mkObj [
 ("id",toJson "frozen-separation-controls"),
 ("F_agreement",toJson (agreement ps pt F0)),("Fprime_agreement",toJson (agreement ps pt Fprime)),
 ("F_refines_P",toJson (IndependentReadout.refined F0 '''+ls(pub['P'])+''')),
 ("F_refines_some_literal_Q",toJson (pubout.any (fun o => IndependentReadout.refined F0 o.partition))),
 ("Fprime_refines_some_literal_Q",toJson (pubout.any (fun o => IndependentReadout.refined Fprime o.partition))),
 ("Fprime_no_larger",toJson (decide (Fprime.length ≤ F0.length))),
 ("local_cost2_agreement",toJson (agreement (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)) (.node (.leaf 1) (.node (.leaf 2) (.leaf 3))) [[1],[2],[3]])),
 ("whole_source_same_address_partition",toJson (DepthOne.forest s (some [false]))),
 ("three_color_rank",toJson (inputRank s (fun x => if C.contains x then 0 else cheapColor A B D x))),
 ("three_color_receipt",IndependentReadout.receiptJson (generate s (fun x => if C.contains x then 0 else cheapColor A B D x) 3)),
 ("one_mass",IndependentReadout.rational (rawQMass 2 out)),
 ("two_identical_occurrences_mass",IndependentReadout.rational (rawQMass 2 (out++out))),
 ("two_identical_raw_occurrences",toJson ((out++out).map IndependentReadout.outputJson))])
end IndependentSeparation
'''
f=P/'src/ReadoutSeparation.lean';f.write_text(s)
(P/'separation-observer-freeze-v1.json').write_text(json.dumps({'source_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'fixture_sha256':hashlib.sha256((R/'fixtures-v1.json').read_bytes()).hexdigest(),'before_execution':True,'frozen_expectations':{'F_agreement':True,'Fprime_agreement':True,'F_refines_P':True,'F_refines_some_literal_Q':False,'Fprime_refines_some_literal_Q':True,'Fprime_no_larger':True,'local_cost2_agreement':True,'three_color_rank':3,'three_color_costs':[2],'one_mass':'1/8','two_identical_occurrences_mass':'1/4'},'scope':'Only the initially frozen mutation/false controls; no new fixture or query implementation'},indent=2)+'\n')
print('Compiled separation-control expectations frozen.')
