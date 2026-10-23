#!/usr/bin/env python3
"""Execute the initially frozen malformed-label/child-order/suppressed-path controls."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;R=P.parent/'sol-preparation-READY-v1/preparation';d=json.loads((R/'fixtures-v1.json').read_text());g=d['fixtures'][0]
def tr(t):return '.leaf '+str(t)if isinstance(t,int)else '(.node ('+tr(t[0])+') ('+tr(t[1])+'))'
def ls(x):return '['+','.join(map(str,x))+']'
s='import IndependentReadout\nopen Lean Universal233 RMAF\nnamespace MalformedObserver\ndef S : Tree := '+tr(g['S'])+'\ndef T : Tree := '+tr(g['T'])+'\ndef A : List Nat := '+ls(g['P'][0])+'\ndef B : List Nat := '+ls(g['P'][1])+'\n'
s+='def swapped : Tree := '+tr([g['S'][1],g['S'][0]])+'\n'
s+='''#eval IndependentReadout.emit (Json.mkObj [
 ("missing_label_selector",IndependentReadout.selector T (A++[999]) B),
 ("duplicate_parent_selector",IndependentReadout.selector T (A++[1]) B),
 ("child_order_same_rooted_topology",toJson (RMAF.sameShape S swapped)),
 ("suppressed_path",toJson (IndependentReadout.hull (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 3)) [0,2])),
 ("transported_parent_hulls",toJson ('''+''.join(''for _ in [])+'''['''+','.join(ls(b)for b in g['P'])+'''].map (IndependentReadout.hull swapped)))])
end MalformedObserver
'''
f=P/'src/ReadoutMalformed.lean';f.write_text(s);(P/'malformed-observer-freeze-v1.json').write_text(json.dumps({'source_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'before_execution':True,'original_fixture_expectations_unchanged':True,'expected_missing_label_selector':None,'expected_duplicate_parent_selector':None,'expected_child_order_same_rooted_topology':True,'expected_suppressed_path':d['malformed_expected']['suppressed_path'],'transport':'Original parent hull address prefixes 0/1 exchange under root-child swap'},indent=2)+'\n')
