#!/usr/bin/env python3
"""One-shot fresh transport review. Keeps all original review/author outputs intact.
Run via bootloops-python with --pilot, then --full. Exact diagnostics and source
hashes are required; source versions and all stdout remain in this directory.
"""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys,time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[5]
BASE=ROOT/'research/rmaf/triple_dp'
RESULT=ROOT/'research/rmaf/results/triple-family-transport-review-replay.json'
MANIFEST=HERE/'source-manifest.json'
ITEMS=[('TripleDP.lean',19),('ConnectedRegions.lean',8),
       ('family/path_route/PathStem.lean',16),('family/cost_route/FamilyAssembly.lean',17),
       ('family/FamilyModel.lean',11),('family/FamilyTrim.lean',16),
       ('family/FamilyGeometry.lean',8),('family/FamilyControls.lean',4),
       ('family/FamilyTransport.lean',9),('family/TransportControls.lean',2)]
SOURCES=[s for s,n in ITEMS]+['family/NegativeTransport.lean']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
if not MANIFEST.exists():
    manifest={s:sha(BASE/s) for s in SOURCES}
    for s in SOURCES:
        p=HERE/'snapshot'/s;p.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(BASE/s,p)
    dump(MANIFEST,manifest)
manifest=json.loads(MANIFEST.read_text())
for s,h in manifest.items():
    assert sha(BASE/s)==h and sha(HERE/'snapshot'/s)==h,('source drift',s)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',(HERE/'snapshot'/s).read_text()),s
prior=json.loads((ROOT/'research/rmaf/results/triple-family-lean-transport-v2.json').read_text())
prior_matches=[]
for r in prior['builds']:
    s=str(Path(r['file']).relative_to('research/rmaf/triple_dp'))
    if s in manifest:
        assert manifest[s]==r['sha256'],s
        prior_matches.append(s)
assert len(prior_matches)==len(manifest)
BUILD=HERE/'build';BUILD.mkdir(exist_ok=True)
LOGS=HERE/'logs';LOGS.mkdir(exist_ok=True)
ENV=dict(os.environ,ELAN_HOME=str(ROOT/'.runtime/elan'),LEAN_PATH=str(BUILD))
records=[]
if (HERE/'pilot.json').exists():records=json.loads((HERE/'pilot.json').read_text())['runs']

def run(name,src,count=None,negative=False):
    args=[str(ROOT/'bootloops-lean')]
    if not negative:args+=['-o',str(BUILD/(src.stem+'.olean'))]
    args+=[str(src)]
    start=time.perf_counter()
    p=subprocess.run(args,cwd=ROOT,env=ENV,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
    seconds=time.perf_counter()-start
    log=LOGS/(name+'.log');log.write_text(p.stdout)
    audits=[]
    for line in p.stdout.splitlines():
        m=re.match(r"'([^']+)' (?:depends on axioms: \[(.*)\]|does not depend on any axioms)",line)
        if m:
            axioms=[a.strip() for a in (m[2] or '').split(',') if a.strip()]
            assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(name,axioms)
            audits.append({'name':m[1],'axioms':axioms})
    if negative:
        assert p.returncode!=0 and p.stdout.count('error:')==1,(name,p.stdout)
        assert 'Tactic `decide` proved that the proposition' in p.stdout,(name,p.stdout)
        assert 'transportedSingleton.cost = 1' in p.stdout and 'is false' in p.stdout,(name,p.stdout)
    else:
        assert p.returncode==0 and 'error:' not in p.stdout and 'sorryAx' not in p.stdout,(name,p.stdout)
        assert len(audits)==count,(name,len(audits),count)
    records.append({'name':name,'source':str(src.relative_to(ROOT)),'sha256':sha(src),
                    'command':args,'exit_code':p.returncode,'seconds':seconds,
                    'log':str(log.relative_to(ROOT)),'axiom_audits':audits,
                    'expected_false':negative,'passed':True})
    print(f'{name}: accepted criterion; audits={len(audits)} exit={p.returncode} seconds={seconds:.3f}',flush=True)

if sys.argv[-1]=='--pilot':
    assert not records
    run('TripleDP',HERE/'snapshot'/ITEMS[0][0],ITEMS[0][1])
    dump(HERE/'pilot.json',{'runs':records});sys.exit(0)
assert sys.argv[-1]=='--full' and len(records)==1
for s,n in ITEMS[1:]:run(Path(s).stem,HERE/'snapshot'/s,n)
run('CleanTransport',HERE/'CleanTransport.lean',0)
run('NegativeTransport',HERE/'snapshot/family/NegativeTransport.lean',negative=True)
for s,h in manifest.items():assert sha(BASE/s)==h,('changed during replay',s)
version=subprocess.run([str(ROOT/'bootloops-lean'),'--version'],cwd=ROOT,env=ENV,text=True,capture_output=True,check=True).stdout.strip()
assert '4.35.0' in version
receipt={'status':'fresh kernel/control replay passed; semantic verdict in transport_review/REPORT.md; full G2 OPEN',
         'version':version,'environment':{'ELAN_HOME':ENV['ELAN_HOME'],'LEAN_PATH':ENV['LEAN_PATH']},
         'runs':records,'source_hashes':manifest,'source_hashes_match_author_v2':prior_matches,
         'author_source_unchanged':True,'forbidden_token_hits':0,
         'new_author_audits':{'FamilyTransport':9,'TransportControls':2},
         'new_author_declaration_kinds':{'theorems':9,'constructors':2},
         'main_module_kinds':{'FamilyTransport':{'theorems':7,'constructors':2}},
         'independent_controls':json.loads((HERE/'exact_transport_controls.json').read_text()),
         'reviewer_code_sha256':{'replay.py':sha(Path(__file__)),'CleanTransport.lean':sha(HERE/'CleanTransport.lean')}}
dump(RESULT,receipt)
print(f'PASS {len(records)}/12 declared stages; exact false proposition rejected and same-import true twin accepted')
