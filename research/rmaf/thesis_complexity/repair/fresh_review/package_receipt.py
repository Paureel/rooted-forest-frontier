"""One-shot receipt and dashboard packager; imports no candidate implementation."""
from pathlib import Path
import json,hashlib,ast
base=Path(__file__).resolve().parent;root=base.parents[4];rmaf=base.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
inputs=[rmaf/'sources/baseline/whidden-thesis-2013.txt',rmaf/'sources/baseline/whidden-thesis-2013.pdf',base.parent/'FRESH-REVIEW-TARGET.md',base.parent/'controls-frozen.json',rmaf/'results/thesis-complexity-reachable-trace.json',rmaf/'results/thesis-complexity-three-credit-trace.json']
for arm,names in [('adversary',['PROOF-ATTEMPT.md','AdversaryArithmetic.lean']),('geometry',['PROOF.md','REVIEW-NOTES.md','Geometry.lean']),('recurrence',['report.md','state-invariant.md','RepairArithmetic.lean'])]:
    inputs.extend(base.parent/arm/n for n in names)
lean=json.loads((base/'lean-compile-receipt.json').read_text())
for r in lean:assert sha(root/r['source'])==r['sha256'],'candidate Lean source changed since clean compilation'
imports={}
for p in base.glob('*.py'):
    if '.failed-' in p.name or '.pre-' in p.name:continue
    mods=[]
    for n in ast.walk(ast.parse(p.read_text())):
        if isinstance(n,ast.Import):mods.extend(a.name for a in n.names)
        if isinstance(n,ast.ImportFrom):mods.append(n.module)
    imports[p.name]=sorted(set(mods))
    assert not any('adversary' in (m or '') or 'recurrence' in (m or '') or 'geometry' in (m or '') for m in mods)
local=json.loads((rmaf/'results/thesis-runtime-repair-fresh-review-exhaustive-local.json').read_text())
interface=json.loads((rmaf/'results/thesis-runtime-repair-fresh-review-interface.json').read_text())
control=json.loads((rmaf/'results/thesis-runtime-repair-fresh-review-controls.json').read_text())
extra=json.loads((rmaf/'results/thesis-runtime-repair-fresh-review-additional.json').read_text())
mut=json.loads((rmaf/'results/thesis-runtime-repair-fresh-review-mutation.json').read_text())
assert not local['fires'] and mut['mutation_rejected'] and mut['Lean_false_copy_rejected']
metrics={'exposed_control_records':len(control['records']),'post_candidate_controls':len(extra['controls']),'local_input_trees':local['input_trees'],'local_qualifying_orientations':local['admissible_orientations'],'frontier_budget_tests':local['frontier_budget_tests'],'source_shape_checks':local['source_shape_checks'],'local_fires':0,'use_site_and_abstract_rows':len(interface['rows']),'multiplicative_passing_rows':interface['multiplicative_passing'],'multiplicative_rows':interface['multiplicative_rows'],'positive_Lean_modules':len(lean),'positive_Lean_theorems':sum(len(r['theorems']) for r in lean),'candidate_mutations_rejected':2,'actual_reachable_negative_budget':-4}
claims=[{'id':'joint-source-bound','label':'Universal source-reachable G4.1 runtime repair','status':'open','detail':'No unconditional acceptance or rejection; source history/frontier mapping and credited A continuation remain.'},{'id':'conditional-composition','label':'Exact A/B/C conditional composition','status':'checked','detail':'With A<=X/4-2 and B<=X/8-3, C<=X/8+2 implies total<=X/2-2; strong C gives slack 3.'},{'id':'finite-local-geometry','label':'Finite conditional local C tests','status':'checked','detail':'708 orientations from 11,340 connected local trees; 5,664 K=0..7 tests; no fire; outside-b imposed; deterministic allowed continuation ties; no reachability inference.'},{'id':'source-Q-convention','label':'Page119 Q assignment','status':'conditional','detail':'Prose adds cut v; displayed recurrence adds protected u. Fixture Q={x,u} uses the displayed equation.'}]
lemmas=[{'id':'active-a-history','label':'Retained active a and protected sibling at G4.1','status':'open','detail':'Explicit unprotected-root histories must establish retained active representative, surviving protected sibling and outside-b pair placement.'},{'id':'A-continuation','label':'Credited A allowance','status':'open','detail':'Generic empty-credit child induction does not imply X/4-2; abstract misuse residual 31 at X=128.'},{'id':'formal-kernels','label':'Final Lean conditional kernels','status':'checked','detail':'All final positive sources recompiled; every theorem axiom-printed; standard logical axioms only. False orientation copy rejected.'}]
artifacts=[str(p.relative_to(root)) for p in [base/'RULING.md',base/'REVIEW.md',base/'README.md',base/'lean-compile-receipt.json']]
receipt={'id':'thesis-runtime-repair-fresh-review','status':'conditional','summary':'Fresh source/control replay, conditional Lean kernels and finite geometry tests completed; source-wide runtime repair remains open.','metrics':metrics,'claims':claims,'lemmas':lemmas,'artifacts':artifacts,'input_lineage':[{'path':str(p.relative_to(root)),'sha256':sha(p)} for p in inputs],'implementation_imports':imports,'independence':'Fresh stdlib forest/arithmetic evaluator; shared thesis and exposed control data; candidate Lean copied only for compilation; no prior checker imports. Finite attack after candidate reading is targeted fresh-code evidence, not held-out verification.','skips':['No exhaustive arbitrary-forest or all-history source-state enumeration.','No universal Lean source-tree formalization.','Full upstream toolkit suite not rerun for review-only files.']}
(rmaf/'results/thesis-runtime-repair-fresh-review-final.json').write_text(json.dumps(receipt,indent=2)+'\n')
dashboard={k:receipt[k] for k in ('id','status','summary','metrics','claims','lemmas','artifacts')};dashboard['title']='Fresh independent G4 runtime repair review'
(rmaf/'progress/thesis-runtime-repair-fresh-review.json').write_text(json.dumps(dashboard,indent=2)+'\n')
print(json.dumps({'status':receipt['status'],'metrics':metrics}))
