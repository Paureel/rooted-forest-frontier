#!/usr/bin/env python3
"""One-task exact scope attack on the standalone wording of thesis Lemma6.3.
Uses tiny forests; does not claim to test Theorem6.12 or 6.13.
"""
import json,itertools
from pathlib import Path
from oracle import Tree,normal


def labels(t):return Tree(t).labelset

def forest_refines_blocks(fine,coarse):
    return all(any(labels(f)<=labels(c) for c in coarse) for f in fine)

def all_triples(forest):
    out=set()
    for spec in forest:
        tree=Tree(spec)
        for triple in itertools.combinations(sorted(tree.labelset),3):
            out.add((triple,tree.block(triple)[1]))
    return out

def spans_in_forest(block,forest):
    for i,spec in enumerate(forest):
        t=Tree(spec)
        if set(block)<=t.labelset:
            return {(i,v) for v in t.block(block)[0]}
    return None

def overlaps(f2,f1):
    # Definition p18: overlap requires two existing non-disjoint paths.
    paths=[]
    for c in f2:
        row=[]
        for pair in itertools.combinations(sorted(labels(c)),2):
            s=spans_in_forest(pair,f1)
            if s is not None:row.append(s)
        paths.append(row)
    return any(a & b for i,row in enumerate(paths) for a in row
               for later in paths[i+1:] for b in later)

f1=['rho','a','b'];f2=['rho',('a','b')]
assert all_triples(f2)==set() and all_triples(f1)==set()
assert not overlaps(f2,f1)
assert not forest_refines_blocks(f2,f1)
# Clean twin: keeping F1=F2 meets the missing containment hypothesis.
assert forest_refines_blocks(f2,f2) and not overlaps(f2,f2)
assert all_triples(f2)<=all_triples(f2)
record={'claim':'Thesis Lemma6.3 standalone arbitrary-forest statement omits component containment',
        'source':'printed p101 / PDF page114; visually inspected',
        'F1':f1,'F2':f2,'all_F2_triples_compatible':True,'no_F2_components_overlap_in_F1':True,
        'F2_can_be_forest_of_F1':False,'reason':'a and b disconnected in F1; edge deletion/suppression cannot connect them',
        'clean_twin_passed':True,'scope':'Does not refute algorithm. Lemma6.3 uses in Lemmas6.4/6.5 have a connected tree as reference, where containment is automatic.',
        'repair':'Retain condition1 of Lemma2.4, or state reference F1 is a tree.'}
p=Path('research/rmaf/results/thesis-transfer-source-scope.json')
p.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
