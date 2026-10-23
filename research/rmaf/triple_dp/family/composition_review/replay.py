#!/usr/bin/env python3
"""One-shot isolated nonauthor replay for the composition review.
Run --pilot first, then --full via bootloops-python. Sources are snapshotted;
all oleans/logs are reviewer owned. This does not prove G2 or graph refinement.
Acceptance checks fail closed on count, exact diagnostic, hash or axiom drift.
"""
from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, sys, time
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BASE = ROOT/'research/rmaf/triple_dp'
RESULT = ROOT/'research/rmaf/results/triple-family-composition-review-replay.json'
MANIFEST = HERE/'source-manifest.json'
SOURCES = [
 'TripleDP.lean','ConnectedRegions.lean', 'family/FamilyModel.lean',
 'family/FamilyTrim.lean','family/FamilyGeometry.lean','family/FamilyControls.lean',
 'family/NegativeFamily.lean','family/REPORT.md',
 'family/path_route/PathStem.lean','family/path_route/Controls.lean',
 'family/path_route/CleanChildWitness.lean','family/path_route/WrongChildWitness.lean',
 'family/path_route/WORK.md','family/path_route/FROZEN-WORK.sha256',
 'family/cost_route/FamilyAssembly.lean','family/cost_route/Controls.lean',
 'family/cost_route/CleanTwin.lean','family/cost_route/FalseMutant.lean','family/cost_route/WORK.md']
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x): p.write_text(json.dumps(x,indent=2)+'\n')
if not MANIFEST.exists():
    manifest = {s:sha(BASE/s) for s in SOURCES}
    for s in SOURCES:
        p = HERE/'snapshot'/s; p.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(BASE/s,p)
    dump(MANIFEST,manifest)
manifest = json.loads(MANIFEST.read_text())
for s,h in manifest.items():
    assert sha(BASE/s)==h, ('live-source-drift',s)
    assert sha(HERE/'snapshot'/s)==h, ('snapshot-drift',s)
# Exact provenance matches, comparing sources rather than author numeric outputs.
prior = json.loads((ROOT/'research/rmaf/results/triple-family-lean-geometry-v1.json').read_text())
prior_matches=[]
for r in prior['builds']:
    s = str(Path(r['file']).relative_to('research/rmaf/triple_dp'))
    assert manifest[s] == r['sha256'], s
    prior_matches.append(s)
cost_prior = json.loads((ROOT/'research/rmaf/results/triple-family-cost-replay.json').read_text())
for s,h in cost_prior['hashes'].items():
    rel = str(Path(s).relative_to('research/rmaf/triple_dp')) if s.startswith('research/rmaf/triple_dp/') else None
    if rel in manifest:
        assert manifest[rel]==h, rel
        prior_matches.append(rel)
frozen = (BASE/'family/path_route/FROZEN-WORK.sha256').read_text().split()[0]
assert manifest['family/path_route/WORK.md']==frozen
scan=[]
for s in SOURCES:
    if s.endswith('.lean'):
        text = (HERE/'snapshot'/s).read_text()
        bad = re.findall(r'\b(?:sorry|admit|axiom|native_decide)\b',text)
        assert not bad,(s,bad)
        scan.append(s)
LOGS=HERE/'logs'; LOGS.mkdir(exist_ok=True)
for d in ['build-geometry','build-cost']:(HERE/d).mkdir(exist_ok=True)
records=[]
if (HERE/'pilot.json').exists(): records=json.loads((HERE/'pilot.json').read_text())['runs']

def run(name, rel, build, audit_count=None, output=True, false_count=0, diagnostic=None):
    src=HERE/'snapshot'/rel
    env=dict(os.environ, ELAN_HOME=str(ROOT/'.runtime/elan'),LEAN_PATH=str(HERE/build))
    args=[str(ROOT/'bootloops-lean')]
    if output: args += ['-o',str(HERE/build/(src.stem+'.olean'))]
    args += [str(src)]
    start=time.perf_counter()
    p=subprocess.run(args,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
    secs=time.perf_counter()-start
    log=LOGS/(name+'.log');log.write_text(p.stdout)
    audits=[]
    for line in p.stdout.splitlines():
        m=re.match(r"'([^']+)' (?:depends on axioms: \[(.*)\]|does not depend on any axioms)",line)
        if m:
            axioms=[a.strip() for a in (m[2] or '').split(',') if a.strip()]
            assert set(axioms)<= {'propext','Classical.choice','Quot.sound'},(name,axioms)
            audits.append({'name':m[1],'axioms':axioms})
    if false_count:
        assert p.returncode!=0,(name,'false proposition accepted')
        assert p.stdout.count('error:')==false_count,(name,p.stdout)
        assert p.stdout.count('is false')==false_count or (diagnostic and diagnostic in p.stdout),(name,p.stdout)
        if diagnostic: assert diagnostic in p.stdout,(name,p.stdout)
    else:
        assert p.returncode==0 and 'error:' not in p.stdout and 'sorryAx' not in p.stdout,(name,p.stdout)
        assert audit_count is not None and len(audits)==audit_count,(name,len(audits),audit_count)
    record={'name':name,'source':rel,'sha256':manifest[rel], 'command':args,
            'env':{'ELAN_HOME':env['ELAN_HOME'],'LEAN_PATH':env['LEAN_PATH']},
            'exit_code':p.returncode,'seconds':secs,'log':str(log.relative_to(ROOT)),
            'axiom_audits':audits,'expected_false_propositions':false_count,'passed':True}
    records.append(record)
    print(f"{name}: accepted declared check; {len(audits)} audits, exit {p.returncode}, {secs:.3f}s",flush=True)

if sys.argv[-1]=='--pilot':
    assert not records,'pilot exists; retain it'
    run('geometry-TripleDP','TripleDP.lean','build-geometry',19)
    dump(HERE/'pilot.json',{'runs':records})
    sys.exit(0)
assert sys.argv[-1]=='--full' and len(records)==1
run('geometry-ConnectedRegions','ConnectedRegions.lean','build-geometry',8)
run('PathStem','family/path_route/PathStem.lean','build-geometry',16)
run('FamilyModel-dependency','family/FamilyModel.lean','build-geometry',11)
run('FamilyTrim-dependency','family/FamilyTrim.lean','build-geometry',16)
run('FamilyGeometry','family/FamilyGeometry.lean','build-geometry',8)
run('path-Controls','family/path_route/Controls.lean','build-geometry',7,output=False)
run('path-clean','family/path_route/CleanChildWitness.lean','build-geometry',1,output=False)
run('path-false','family/path_route/WrongChildWitness.lean','build-geometry',output=False,false_count=1,diagnostic='is false')
run('FamilyControls-dependency','family/FamilyControls.lean','build-geometry',4)
run('FamilyNegative-dependency','family/NegativeFamily.lean','build-geometry',output=False,false_count=1,diagnostic='0 = 1')
run('cost-TripleDP','TripleDP.lean','build-cost',19)
run('cost-ConnectedRegions','ConnectedRegions.lean','build-cost',8)
run('FamilyAssembly','family/cost_route/FamilyAssembly.lean','build-cost',17)
run('cost-Controls','family/cost_route/Controls.lean','build-cost',11)
run('cost-clean','family/cost_route/CleanTwin.lean','build-cost',0,output=False)
run('cost-false','family/cost_route/FalseMutant.lean','build-cost',output=False,false_count=2,diagnostic='adjacentSameColor.blockCount = 1')
for s,h in manifest.items(): assert sha(BASE/s)==h,(s,'changed during replay')
version=subprocess.run([str(ROOT/'bootloops-lean'),'--version'],cwd=ROOT,text=True,capture_output=True,check=True).stdout.strip()
assert '4.35.0' in version
receipt={'status':'kernel/control replay passed; semantic conclusions in composition_review/REPORT.md; G2 OPEN',
         'version':version,'runs':records,'sources':manifest,'source_hashes_match_prior_receipts':sorted(set(prior_matches)),
         'forbidden_source_scan':{'files':scan,'tokens':['sorry','admit','axiom','native_decide'],'hits':0},
         'source_unchanged_after':True,'reviewer_script_sha256':sha(Path(__file__)),
         'main_audit_counts':{'PathStem':16,'FamilyGeometry':8,'FamilyAssembly':17},
         'independent_exact_controls':json.loads((HERE/'exact_graph_check.json').read_text())}
dump(RESULT,receipt)
print(f'PASS {len(records)}/17 declared replay stages; source hashes unchanged; receipt {RESULT}')
