#!/usr/bin/env python3
"""One-shot encoding of pinned constructed fixture trees into Lean controls."""
from pathlib import Path
import local
D=Path(__file__).resolve().parent
all_labels=sorted({x for t,u,_ in local.fixture_family().values() for x in local.labels(t)})
ids={x:i for i,x in enumerate(all_labels)}
def tr(t):return f'.leaf {ids[t]}' if local.leaf(t) else f'.node ({tr(t[0])}) ({tr(t[1])})'
def block(X):return '['+','.join(str(ids[x]) for x in X)+']'
def forest(F):return '['+','.join(block(B) for B in F)+']'
txt='import Rule5Defs\nnamespace Universal233.Rule5Local.Pre\nopen RMAF HardParent CherryBranching\nset_option maxRecDepth 8000\n'
for name,(t,u,k) in local.fixture_family().items():
 txt+=f'def {name}T : Tree := {tr(t)}\ndef {name}S : Tree := {tr(u)}\n'
 txt+=f'theorem {name}_admitted : admitted {name}T {name}S {ids["a"]} {ids["b"]} = true := by decide\n'
 if k in ['321','322','323','common']:
  C=local.classify(t,u);X=C['P'][C['j']]
  txt+=f'theorem {name}_incident : (incident {name}T {block(X)}).length = {1 if k=="common" else 2} := by decide\n'
  if k=='common':txt+=f'theorem common_emits : (commonSplit? commonT commonS {ids["a"]} {ids["b"]} {block(X)}).isSome = true := by decide\n'
t,u,_=local.fixture_family()['first'];F=[['a','c'],['b'],['w'],['x'],['p'],['q'],['s']];G=[['a','b'],['c'],['w'],['x'],['p'],['q'],['s']]
txt+=f'def strictF : List (List Nat) := {forest(F)}\ndef exchangeG : List (List Nat) := {forest(G)}\n'
txt+='theorem strict_valid : agreement firstT firstS strictF = true := by decide\n'
txt+='theorem replacement_valid : agreement firstT firstS exchangeG = true := by decide\n'
txt+='theorem exchange_no_larger : exchangeG.length = strictF.length := by decide\n'
txt+=f'theorem strict_not_refines : refinesCheck strictF (pendantPartition firstS {ids["a"]} {ids["b"]}) = false := by decide\n'
missing=(('a','b'),('c',(('x','y'),'z')))
txt+=f'def missingT : Tree := {tr(missing)}\ntheorem missing_priority_rejected : earlierClear missingT sixS = false := by decide\n'
clear=(('a','b'),(('y','s'),('x',('z','c'))))
txt+=f'def clearanceT : Tree := {tr(clear)}\ntheorem clearance_rejected : pairwiseEmbeddings clearanceT (pendantPartition (.node sixS (.leaf {ids["s"]})) {ids["a"]} {ids["b"]}) = false := by decide\n'
txt+='end Universal233.Rule5Local.Pre\n'
(D/'Rule5PreControls.lean').write_text(txt)
bad='import Rule5PreControls\nopen RMAF Universal233.Rule5Local Universal233.Rule5Local.Pre Universal233.CherryBranching\n'
bad+='example : earlierClear missingT sixS = true := by decide\n'
bad+=f'example : pairwiseEmbeddings clearanceT (pendantPartition (.node sixS (.leaf {ids["s"]})) {ids["a"]} {ids["b"]}) = true := by decide\n'
bad+='example : ([1,2,3] : List Nat).length = 2 := by decide\n'
bad+=f'example : refinesCheck strictF (pendantPartition firstS {ids["a"]} {ids["b"]}) = true := by decide\n'
(D/'Rule5FalsePreControls.lean').write_text(bad)
(D/'LABELS-v1.json').write_text(__import__('json').dumps(ids,indent=2)+'\n')
