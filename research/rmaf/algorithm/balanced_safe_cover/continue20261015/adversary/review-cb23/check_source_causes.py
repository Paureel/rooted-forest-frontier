#!/usr/bin/env python3
"""One-shot finite source-cause reconstruction and RESULT empty-wrapper control."""
import json,sys,itertools,hashlib,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import compare_cb23 as C
X=C.X
RPATH=Path('research/rmaf/results/algorithm-balanced-cover-continue-cb3-obstruction.json')
R=json.loads(RPATH.read_text());S,T=X.Tree(R['source']),X.Tree(R['target']);ids={frozenset(e['child_labels']):e['edge'] for e in R['original_source_edges']};M={e:ids[L] for e,L in C.edge_clades(S).items()};causes={};t=time.perf_counter()
def add(mask,cause):causes.setdefault(C.remap(mask,M),[]).append(cause)
for A in itertools.combinations(S.labels,3):
 if S.triple(A)!=T.triple(A):add(S.path(A[0],A[1])[1]|S.path(A[0],A[2])[1],{'kind':'triple','labels':list(A)})
for Q in itertools.combinations(S.labels,4):
 a=Q[0]
 for b in Q[1:]:
  c,d=[x for x in Q if x not in (a,b)];V,E=S.path(a,b);W,F=S.path(c,d)
  if not V&W and T.path(a,b)[0]&T.path(c,d)[0]:add(E|F,{'kind':'path-overlap','pairs':[[a,b],[c,d]]})
def canon(c):return json.dumps(c,sort_keys=True)
expected={x['mask']:sorted(map(canon,x['causes'])) for x in R['original_conflicts']}
assert {h:sorted(map(canon,Cs)) for h,Cs in causes.items()}==expected
assert len(causes)==26
sys.path.insert(0,str(Path('research/rmaf/algorithm/balanced_safe_cover/continue20261015').resolve()))
import conflict_row_selector as P
clean=P.solve(None,None,0);assert clean['status']=='SOLVED' and clean['cost']==0
try:P.solve(None,None,-1)
except ValueError:empty_rejected=True
else:empty_rejected=False
assert empty_rejected
actual_hashes={str(Path(p)):hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in R['hashes']}
result={'status':'SOURCE_CAUSES_CONFIRMED_EMPTY_WRAPPER_TEXT_FINDING','original_conflict_rows':len(causes),'original_cause_count':sum(map(len,causes.values())),'all_original_causes_exact_match':True,'empty_clean_budget_zero_solved':True,'empty_n_minus_one_budget_rejected':empty_rejected,'text_finding':'RESULT.md line63 optimization wrapper requires max(0,n-1) or an explicit nonempty precondition','hashes_match_pinned_receipt':{p:actual_hashes[p]==h for p,h in R['hashes'].items()},'seconds':time.perf_counter()-t}
Path('research/rmaf/results/algorithm-balanced-cover-continue-review-cb23-source-causes-v1.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
