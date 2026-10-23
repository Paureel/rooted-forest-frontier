#!/usr/bin/env python3
"""One-shot local handoff assembly, not a proof instrument or general framework.

Toolkit consulted: Emitall checks receipt transcription, not dependency archiving
or PDF layout. Standard shutil/json/hashlib suffice for this finite package.
No theorem is rerun and no compiled object is included. Run from workspace root.
"""
from pathlib import Path
import hashlib, json, re, shutil

ROOT = Path(__file__).resolve().parents[3]
DEST = Path(__file__).resolve().parent
BASE = ROOT / 'research/rmaf/algorithm/universal233/ordinary_dispatch'
PHASE = ROOT / 'research/rmaf/monitoring/resume-complete-proof-20261022'
origins = []

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(src, dst):
    src, dst = Path(src), DEST / dst
    dst.parent.mkdir(parents=True, exist_ok=True)
    if dst.exists():
        assert dst.read_bytes() == src.read_bytes(), f'preserve existing {dst}'
    else: shutil.copyfile(src, dst)
    assert sha(src) == sha(dst)
    origins.append(dict(bundle_path=str(dst.relative_to(DEST)),
                        original_relative_path=str(src.relative_to(ROOT)),
                        sha256=sha(src), bytes=src.stat().st_size))

algo = BASE / 'ram_full_solver_spec_20261022/math_pseudocode_v1'
for f in sorted(algo.iterdir()):
    if f.is_file(): copy(f, Path('algorithm') / f.name)
amend = BASE / 'ram_full_solver_spec_20261022/math_projection_amendment_v2'
for f in sorted(amend.iterdir()):
    if f.is_file(): copy(f, Path('algorithm/projection-v2') / f.name)
copy(amend/'PROJECTION-AMENDMENT-v2.md', 'algorithm/PROJECTION-AMENDMENT-v2.md')
copy(PHASE/'MATHEMATICAL-ENTRY-CONVENTION-AMENDMENT-v2.txt', 'algorithm/ENTRY-v2.txt')
for f in sorted((PHASE/'final-cold-proposed-proof-public-v1').iterdir()):
    if f.is_file(): copy(f, Path('mathematics')/f.name)
for f in sorted((PHASE/'final-cold-computation-public-v1').iterdir()):
    if f.is_file(): copy(f, Path('interfaces')/f.name)
for f in sorted((PHASE/'final-cold-extra-computation-public-v1').iterdir()):
    if f.is_file(): copy(f, Path('interfaces/extra')/f.name)
for f in sorted((PHASE/'selected-paid-prepare-public-v1').iterdir()):
    if f.is_file(): copy(f, Path('interfaces/prepare')/f.name)
copy(BASE/'ram_full_solver_spec_20261022/math_scalar_catalogue_v1/METER-RECEIPT-TYPE-v1.json',
     'interfaces/legacy/METER-RECEIPT-TYPE-v1.json')
copy(PHASE/'pure-optimizer-primitive-types-public-v1/TYPES.json',
     'interfaces/legacy/OPTIMIZER-PRIMITIVE-TYPES-v1.json')
copy(PHASE/'PURE-OPTIMIZER-PRIMITIVES-RELEASE-v1.json',
     'interfaces/legacy/PURE-OPTIMIZER-PRIMITIVES-RELEASE-v1.json')
copy(BASE/'ram_full_solver_spec_20261022/math_scalar_catalogue_v1/MULTIPLICATION-AND-POWER-SYNTAX-v1.txt',
     'interfaces/legacy/MULTIPLICATION-AND-POWER-SYNTAX-v1.txt')

# Sources from separate original providers are never merged into one pool.
def paths(f): return [Path(p) for p in json.loads(f.read_text())]
functional = paths(BASE/'correctness_join_20261022/FINAL-LEAN-PATH-v1.json')
source = paths(BASE/'source_cost_join_20261022/SOURCE-LEAN-PATH-v1.json')
semantic = paths(BASE/'ram_global_completion_20261022/WHOLE-SEMANTIC-BOUNDARY-LEAN-PATH-v1.json')
semantic_roots = sorted({f.stem for p in semantic[1:] for f in p.glob('*.lean')
                         if not any(w in f.stem.lower() for w in ['audit','control','metadata','print','inspect','export','discovery','typecheck'])})
contexts = {
 'functional': (functional, ['WholeFunctional']),
 'source-bound': (source, ['ExplicitSourceOptimizer']),
 'runtime-interfaces': (semantic, semantic_roots),
 'separate-functional-assembly': ([BASE/'clean_whole_assembly_20261022']+functional, ['WholeQueryAssembly']),
 'separate-source-assembly': ([BASE/'source_optimizer_fresh_reconstruction_20261022']+source, ['SealedJoinV1']),
}
pool_paths = []
for ps, _ in contexts.values():
    for p in ps:
        if p not in pool_paths: pool_paths.append(p)
pool_ids = {p:f'p{i:02d}-{p.name}' for i,p in enumerate(pool_paths)}
source_map, ctxs, orders = {}, {}, {}
known_pins = {}
native=json.loads((PHASE/'WHOLE-SEMANTIC-NATIVE-CONTEXT-v1.json').read_text())
for x in native['ordered_project_providers']: known_pins[Path(x['source'])]=x['source_sha256']
for x in json.loads((BASE/'correctness_join_20261022/FINAL-PROJECT-IMPORT-PINS-v1.json').read_text()):
    known_pins[Path(x['source'])]=x['source_sha256']

def imports(text):
    # Header imports only; all project names are ordinary unquoted module names.
    text = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    out=[]
    for line in text.splitlines():
        s=line.split('--',1)[0].strip()
        if not s: continue
        m=re.fullmatch(r'(?:(?:public|private)\s+)?import\s+(.+)',s)
        if m: out.extend(m.group(1).split()); continue
        if s.startswith(('prelude','module')): continue
        break
    return out

for context,(providers,roots) in contexts.items():
    completed, active, order, external = {}, set(), [], set()
    def visit(mod):
        if mod in completed: return completed[mod]
        if mod in active: raise ValueError(f'cyclic import: {context}/{mod}')
        rel=Path(*mod.split('.')).with_suffix('.lean')
        match=next(((p,p/rel) for p in providers if (p/rel).exists()),None)
        if match is None:
            if mod.split('.')[0] in {'Lean','Std','Init','Lake'}:
                external.add(mod); return None
            raise FileNotFoundError(f'{context}: missing exact module {mod}')
        pool,f=match; active.add(mod)
        deps=imports(f.read_text())
        for dep in deps: visit(dep)
        active.remove(mod)
        target=Path('formal/pools')/pool_ids[pool]/rel
        if str(target) not in source_map:
            if f in known_pins: assert sha(f)==known_pins[f],f'frozen source drift {f}'
            copy(f,target)
            source_map[str(target)]={'module':mod,'original_relative_path':str(f.relative_to(ROOT)),
                'sha256':sha(f),'frozen_pin_matched':f in known_pins,'imports':deps}
        completed[mod]=str(target);order.append({'module':mod,'source':str(target),'pool':pool_ids[pool]})
        return str(target)
    for root in roots: visit(root)
    ctxs[context]={'provider_order':[f'formal/pools/{pool_ids[p]}' for p in providers],
                   'roots':roots,'resolved_modules':completed,'standard_modules':sorted(external)}
    orders[context]=order

(DEST/'formal/CONTEXTS.json').write_text(json.dumps(ctxs,indent=2)+'\n')
(DEST/'formal/SOURCE-MAP.json').write_text(json.dumps(source_map,indent=2)+'\n')
(DEST/'formal/BUILD-ORDER.json').write_text(json.dumps(orders,indent=2)+'\n')
(DEST/'formal/lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')

for owner in ['final-cold-semantic-review-20261023','final-cold-cost-review-20261023']:
    d=ROOT/'research/rmaf/algorithm/verification'/owner
    for sub in ['phase-a','phase-b','phase-b-prepare-followon-v1','phase-c']:
        if not (d/sub).exists():continue
        for f in sorted((d/sub).rglob('*')):
            if f.is_file() and '__pycache__' not in f.parts:
                copy(f,Path('verification/final-reviews')/owner/sub/f.relative_to(d/sub))
for f in ['MATHEMATICAL-ACCEPTANCE-v1.json','MATHEMATICAL-COMPLETION-SEAL-v1.json',
          'FINAL-COLD-REVIEW-TARGET-v1.txt','FINAL-COLD-SEMANTIC-PHASE-C-ROOT-REVIEW-v1.json',
          'FINAL-COLD-COST-PHASE-C-ROOT-REVIEW-v1.json','WHOLE-SEMANTIC-PROVIDER-BINDING-v1.json',
          'SELECTED-COMMON-BOUNDARY-ROOT-REVIEW-v1.json','TARGET-v3.txt']:
    copy(PHASE/f,Path('verification/original-records')/f)
for f in ['FINAL-FUNCTIONAL-RECEIPT-v1.json','FINAL-PROJECT-IMPORT-PINS-v1.json']:
    copy(BASE/'correctness_join_20261022'/f,Path('verification/original-records')/f)
copy(BASE/'source_cost_join_20261022/FINAL-SOURCE-RECEIPT-v1.json','verification/original-records/FINAL-SOURCE-RECEIPT-v1.json')
# Source-only audit programs are evidence/context, not an automatic replay service.
for f in ['FinalSourceAudit.lean','MeterAudit.lean']:
    copy(BASE/'source_cost_join_20261022'/f,Path('verification/audit-sources')/f)
(DEST/'ORIGINS.json').write_text(json.dumps(origins,indent=2)+'\n')
print(json.dumps({'copied_files':len(origins),'project_source_files':len(source_map),
 'project_source_bytes':sum((DEST/f).stat().st_size for f in source_map),
 'contexts':{c:len(x['resolved_modules']) for c,x in ctxs.items()},
 'bytes_before_pdf':sum(f.stat().st_size for f in DEST.rglob('*') if f.is_file())}))
