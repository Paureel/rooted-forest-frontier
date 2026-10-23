"""Candidate-copy falsification: remove the load-bearing orientation premise."""
from fresh_checker import *
import subprocess
base=Path(__file__).resolve().parent;workspace=base.parents[4]
source=base.parent/'adversary/PROOF-ATTEMPT.md'
text=source.read_text();assert 'x is no shallower than y' in text
mutated=text.replace('x is no shallower than y','there is no orientation restriction')
(base/'candidate-copy-without-orientation.md').write_text(mutated)
f=json.loads((ROOT/'thesis_complexity/repair/controls-frozen.json').read_text())['controls'][3]
st=set_prot(State(parse(f['F1']),[parse(f['F2'])]),f['protected_F1'],f['protected_F2'])
info=classify(st,('x','y'),require_orientation=False);C=apply(st,next(b for b in info['branches'] if b['name']=='C'))
nextinfo=classify(C,choices(C)[0]);live=[b for b in nextinfo['branches'] if b['legal']]
assert live and min(len(b['cuts']) for b in live)<3
bug={'failing_step':'adversary geometric argument 3/5 with orientation premise removed on copy','exact_instance':f,'scope':'local; wrong orientation is rejected by source model, not a reachable counterexample','lhs':min(len(b['cuts']) for b in live),'rhs':3,'residual':min(len(b['cuts']) for b in live)-3,'mutation_rejected':True,'next_case':nextinfo,'candidate_copy_sha256':hashlib.sha256(mutated.encode()).hexdigest()}
# Clean reverse twin must pass the same minimum-cut assertion.
info=classify(st,('y','x'));C=apply(st,next(b for b in info['branches'] if b['name']=='C'));ni=classify(C,choices(C)[0]);assert min(len(b['cuts']) for b in ni['branches'] if b['legal'])>=3
bug['clean_reverse_twin_passed']=True
# A kernel must also reject a known false candidate lemma with the premise deleted.
s=(base.parent/'geometry/Geometry.lean').read_text();assert '(orient : hy ≤ hx)' in s
s=s.replace('(orient : hy ≤ hx)','(orient : True)')
p=base/'GeometryWithoutOrientation.lean';p.write_text(s)
run=subprocess.run([str(workspace/'bootloops-lean'),str(p)],cwd=workspace,text=True,capture_output=True,timeout=30)
(base/'GeometryWithoutOrientation.log').write_text(run.stdout+run.stderr);assert run.returncode!=0
bug['Lean_false_copy_rejected']=True;bug['Lean_exit_code']=run.returncode
(ROOT/'results/thesis-runtime-repair-fresh-review-mutation.json').write_text(json.dumps(bug,indent=2)+'\n')
print(json.dumps({k:bug[k] for k in ('mutation_rejected','lhs','rhs','residual','clean_reverse_twin_passed','Lean_false_copy_rejected')}))
