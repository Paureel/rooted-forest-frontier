#!/usr/bin/env python3
"""One-shot problem-specific Lean receipt driver; no mathematical evaluator."""
from pathlib import Path
import datetime, hashlib, json, os, re, shutil, subprocess, sys, time
ROOT = Path(__file__).resolve().parents[6]
OWN = Path(__file__).resolve().parent
STAMP = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
OUT = ROOT / 'research/rmaf/results' / ('triple-family-transitions-geometry-' + STAMP)
OUT.mkdir(parents=True)
(OUT/'olean').mkdir()
(OUT/'source').mkdir()
ENV = os.environ.copy()
ENV['ELAN_HOME'] = str(ROOT/'.runtime/elan')
ENV['LEAN_PATH'] = str(OUT/'olean')
records=[]
def record_hashes():
    hashes={str(p.relative_to(OUT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((OUT/'source').iterdir())}
    (OUT/'source-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
def execute(name, args, negative=False):
    start=time.monotonic()
    proc=subprocess.run(args, cwd=ROOT, env=ENV, text=True, capture_output=True, timeout=90)
    log=proc.stdout+proc.stderr
    (OUT/(name+'.log')).write_text(log)
    passed=(proc.returncode != 0 and "Tactic `decide` proved that the proposition" in log) if negative else proc.returncode == 0
    row=dict(name=name, command=args, exit=proc.returncode, elapsed_seconds=time.monotonic()-start,
             expected='false-proposition rejection' if negative else 'compile', passed=passed)
    records.append(row)
    (OUT/'runs.json').write_text(json.dumps(records,indent=2)+'\n')
    print(json.dumps(row),flush=True)
    if not passed: raise SystemExit('FAILED: '+name+'; receipt '+str(OUT))
def compile(name, source, negative=False):
    target=OUT/'source'/(name+'.lean')
    shutil.copyfile(source,target)
    record_hashes()
    execute(name, [str(ROOT/'bootloops-lean'),'-o',str(OUT/'olean'/(name+'.olean')),str(target)],negative)
print('RECEIPT '+str(OUT),flush=True)
for p in [OWN/'CONTROLS.md',OWN/'run.py',ROOT/'research/rmaf/triple_dp/family/transitions/TARGET.md',ROOT/'research/rmaf/triple_dp/family/transitions/controls.json']:
    shutil.copyfile(p,OUT/'source'/p.name)
execute('version',[str(ROOT/'bootloops-lean'),'--version'])
for name,path in [('TripleDP','research/rmaf/triple_dp/TripleDP.lean'),
                  ('ConnectedRegions','research/rmaf/triple_dp/ConnectedRegions.lean'),
                  ('FamilyAssembly','research/rmaf/triple_dp/family/cost_route/FamilyAssembly.lean')]:
    compile(name,ROOT/path)
for name in ['GeometrySupportDefs','GeometryPositive']:
    compile(name,OWN/(name+'.lean'))
for name in ['GeometryFalseRoot','GeometryFalseBranch']:
    compile(name,OWN/(name+'.lean'),negative=True)
if '--proof' in sys.argv:
    compile('MergeGeometry',OWN/'MergeGeometry.lean')
    src=(OUT/'source/MergeGeometry.lean').read_text()
    log=(OUT/'MergeGeometry.log').read_text()
    names=re.findall(r'^#print axioms (\w+)$',src,re.M)
    axioms=set()
    for group in re.findall(r'depends on axioms: \[([^]]*)\]',log):
        axioms.update(x.strip() for x in group.split(',') if x.strip())
    assert len(names)==17 and len(set(names))==17
    assert all("'TripleDP.GeometryRoute."+name+"'" in log for name in names)
    assert axioms <= {'propext','Quot.sound','Classical.choice'}
    assert 'sorryAx' not in log
    for name in ['GeometrySupportDefs','MergeGeometry']:
        source=(OUT/'source'/(name+'.lean')).read_text()
        assert not re.search(r'\b(?:sorry|admit|native_decide|axiom)\b',source)
    (OUT/'axiom-audit.json').write_text(json.dumps(dict(queried=len(names),axioms=sorted(axioms),passed=True),indent=2)+'\n')
hashes={str(p.relative_to(OUT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((OUT/'source').iterdir())}
(OUT/'source-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
(OUT/'PASS.json').write_text(json.dumps(dict(passed=True,commands=len(records),scope='support geometry only',fresh_nonauthor=False),indent=2)+'\n')
print('PASS receipt '+str(OUT),flush=True)
