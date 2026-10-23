from pathlib import Path
import hashlib, json, os, re, subprocess, time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[5]
RESULTS = ROOT / 'research/rmaf/results'
PREFIX = 'thesis-correctness-repair-edge-second-'
AUDIT = HERE / 'lean-audit'
AUDIT.mkdir(exist_ok=True)
ENV = dict(os.environ, LEAN_PATH=str(AUDIT))
FILES = ['ParentTransport.lean', 'YieldTransport.lean', 'SecondCut.lean', 'PositiveControls.lean', 'NegativeControl.lean']
PRODUCTION = FILES[:3]
allowed = {'propext', 'Quot.sound', 'Classical.choice'}
source_hashes = {}
commands = []
started = time.perf_counter()
for name in FILES:
    source = HERE / name
    body = source.read_text()
    source_hashes[name] = hashlib.sha256(source.read_bytes()).hexdigest()
    assert not re.search(r'\b(sorry|axiom|native_decide)\b', body), name
    cmd = [str(ROOT / 'bootloops-lean')]
    if name in PRODUCTION:
        cmd += ['-o', str(AUDIT / name.replace('.lean', '.olean'))]
    cmd += [str(source)]
    t0 = time.perf_counter()
    result = subprocess.run(cmd, cwd=ROOT, env=ENV, text=True, capture_output=True)
    elapsed = time.perf_counter() - t0
    output = result.stdout + result.stderr
    log = RESULTS / f'{PREFIX}audit-{name[:-5]}.log'
    log.write_text(output)
    negative = name == 'NegativeControl.lean'
    if negative:
        assert result.returncode != 0 and 'is false' in output, output
    else:
        assert result.returncode == 0, output
    axioms = set()
    for block in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', output, re.S):
        axioms.update(a.strip() for a in block.split(',') if a.strip())
    assert axioms <= allowed, axioms
    commands.append(dict(file=str(source), command=cmd, returncode=result.returncode,
                         expected_failure=negative, log=str(log),
                         elapsed_seconds=elapsed, axiom_union=sorted(axioms)))
old_audit = json.loads((RESULTS / 'thesis-correctness-repair-edge-formal-audit.json').read_text())
v1_unchanged = {
    name: hashlib.sha256((HERE.parent / name).read_bytes()).hexdigest() == digest
    for name, digest in old_audit['source_hashes'].items()
}
assert all(v1_unchanged.values())
for line in (HERE / 'input-freeze.sha256').read_text().splitlines():
    digest, name = line.split(maxsplit=1)
    assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest, name
report = dict(
    status='SCOPED-LOCAL-TRANSPORT-CHECKS-PASS',
    named_production_theorems=sum(len(re.findall(r'\btheorem\s+', (HERE / n).read_text())) for n in PRODUCTION),
    production_files=PRODUCTION,
    controls_positive_named=len(re.findall(r'\btheorem\s+', (HERE / 'PositiveControls.lean').read_text())),
    positive_closed_examples=len(re.findall(r'\bexample\s*:', (HERE / 'PositiveControls.lean').read_text())),
    negative_control_rejected=True,
    fresh_import_directory=str(AUDIT), import_environment={'LEAN_PATH': str(AUDIT)},
    source_hashes=source_hashes, commands=commands,
    v1_source_hashes_unchanged=v1_unchanged,
    input_freeze_rechecked=True,
    elapsed_seconds=time.perf_counter()-started,
    formal_scope='Exact parent maps and concrete recursive cut/yield semantics for two explicitly witnessed pendant splices, preserving original surviving node IDs. No AF premise.',
    unproved_formal_interface='Derive the two-splice certificate and original-ID tree encoding from the general reduced binary parent-graph 2B geometry.',
    universal_AF_normalization='NOT_CLAIMED', global_correctness='NOT_CLAIMED')
out = RESULTS / f'{PREFIX}formal-audit.json'
out.write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps({'receipt': str(out), 'theorems': report['named_production_theorems'], 'status':report['status'], 'elapsed_seconds':report['elapsed_seconds'], 'v1_unchanged':all(v1_unchanged.values())}, indent=2))
