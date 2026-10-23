"""One-shot source append-copy accounting control; not a machine cost interpreter."""
from pathlib import Path
from hashlib import sha256
import json,time
H=Path(__file__).resolve().parent
def comb(n):
 t=0
 for i in range(1,n):t=[t,i]
 return t
def leaves_with_copies(t):
 if isinstance(t,int):return [t],0
 a,wa=leaves_with_copies(t[0]);b,wb=leaves_with_copies(t[1]);return a+b,wa+wb+len(a)
start=time.perf_counter();e=json.loads((H/'COST-CONTROL-EXPECTATIONS-v1.json').read_text());known=[]
for c in e['known']:
 labels,copies=leaves_with_copies(comb(c['leaves']));assert len(labels)==c['leaves'] and copies==c['leftCombCopies'];known.append(c)
c=e['counterexample'];labels,copies=leaves_with_copies(comb(c['leaves']));total=len(labels)*copies;author=4*c['n']*(c['m']+c['r']+1)
assert copies==c['leftCombCopiesPerOwnerQuery'] and total==c['constructionCopiesOnly'] and author==c['authorDisplayedOwnerBound'] and total>author
caught=False
try:assert (c['leaves']-1)==c['leftCombCopiesPerOwnerQuery']
except AssertionError:caught=True
assert caught
out={'status':'DISPLAYED-OWNER-SUBBOUND-REFUTED-IN-SOURCE-COPY-MODEL','expectationsSHA256':sha256((H/'COST-CONTROL-EXPECTATIONS-v1.json').read_bytes()).hexdigest(),'known':known,'counterexample':c,'observedCopies':total,'observedAuthorBound':author,'negativeControlCaught':caught,'seconds':time.perf_counter()-start,'scope':e['scope']};(H/'cost-copy-control-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
