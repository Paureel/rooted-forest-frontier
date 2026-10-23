#!/usr/bin/env python3
"""One-shot hypothesis test for synergistic genuine degree-two vertex marks.
Expected values are in JOURNAL.md before this script's first execution.
"""
import hashlib,json
from pathlib import Path
from check_geometry import Tree,local_candidates,opt,assert_equal
root=Path(__file__).resolve().parents[3]
t=Tree(((0,3),(1,(2,4))));d=Tree(((0,2),1));span=t.span(d.labels)
v=next(iter(t.adj[t.labels[0]]));w=next(iter(t.adj[t.labels[2]]))
assert_equal(t.degree(v,span),2);assert_equal(t.degree(w,span),2)
candidates=local_candidates(t,d)
queries=[opt(candidates,marks) for marks in [set(),{v},{w},{v,w}]]
values=[q['cost'] for q in queries];assert_equal(values,[1,1,1,2])
report={'status':'refuted-additive-penalties','target':t.syntax,'source':d.syntax,'marks':[v,w],'degrees':[2,2],'costs_empty_v_w_vw':values,'witnesses':[q['blocks'] for q in queries],'individual_penalties':[0,0],'joint_penalty':1,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256((Path(__file__).parent/'check_geometry.py').read_bytes()).hexdigest()}
(root/'results/pure-bridge-mark-interaction.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
