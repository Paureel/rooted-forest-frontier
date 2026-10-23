"""One-shot replay of conditional finite charge theorems and development controls.
Outputs are additive; every attempt gets fresh source, .olean, and log directories.
No theorem status depends on a compiler exit alone: query, axiom, and false-goal
checks are mandatory. This script is not a fresh nonauthor scientific review.
"""
from pathlib import Path
import os, sys, re, subprocess, hashlib, json, time, datetime, shutil

BASE=Path(__file__).resolve().parent
ROOT=Path.cwd()
LABEL=sys.argv[1] if len(sys.argv)>1 else str(time.time_ns())
assert re.fullmatch(r'[a-zA-Z0-9_-]+',LABEL)
RUN=BASE/'replays'/LABEL
RUN.mkdir(parents=True,exist_ok=False)
SNAP=RUN/'source'; SNAP.mkdir()
LOG=RUN/'logs'; LOG.mkdir()
RESULT=ROOT/f'research/rmaf/results/triple-family-transitions-restriction-charge-replay-{LABEL}.json'
assert not RESULT.exists()
env=dict(os.environ,ELAN_HOME=str(ROOT/'.runtime/elan'),LEAN_PATH=str(SNAP))
rows=[]
receipt={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'grade':'IN-PROGRESS','run':str(RUN.relative_to(ROOT)),'rows':rows}

def run(name,cmd,environment=env):
    start=time.perf_counter()
    p=subprocess.run(cmd,cwd=ROOT,env=environment,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=LOG/f'{name}.log'; log.write_text(p.stdout)
    row={'name':name,'exit':p.returncode,'seconds':time.perf_counter()-start,
         'log':str(log.relative_to(ROOT)),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
    rows.append(row); print(json.dumps(row),flush=True)
    return p

try:
    frozen=BASE/'FROZEN_CONTROLS.json'
    shutil.copy2(frozen,SNAP/frozen.name)
    shutil.copy2(BASE/'controls.py',SNAP/'controls.py')
    cresult=ROOT/f'research/rmaf/results/triple-family-transitions-restriction-charge-controls-{LABEL}.json'
    p=run('numerical-controls',[str(ROOT/'bootloops-python'),str(SNAP/'controls.py'),str(cresult)])
    assert p.returncode==0,p.stdout
    # Retain a real source-copy mutation. It keeps positives unchanged and
    # disables equality checking, so all eight wrong outputs must escape.
    mutant=(SNAP/'controls.py').read_text().replace('return actual == expected','return True')
    assert mutant != (SNAP/'controls.py').read_text()
    (SNAP/'controls_mutant.py').write_text(mutant)
    p=run('comparator-mutant',[str(ROOT/'bootloops-python'),str(SNAP/'controls_mutant.py'),str(cresult)+'.mutant'])
    assert p.returncode!=0 and 'wrong-output comparator escaped' in p.stdout,p.stdout
    data=json.loads(frozen.read_text())
    for c in data['wrong_numbers']+data['corruptions']: assert c['id'] in p.stdout,c['id']
    assert not Path(str(cresult)+'.mutant').exists()
    mods=[ROOT/'research/rmaf/triple_dp/TripleDP.lean',ROOT/'research/rmaf/triple_dp/ConnectedRegions.lean',
          ROOT/'research/rmaf/triple_dp/family/cost_route/FamilyAssembly.lean']
    mods += [BASE/n for n in ['ChargeCore.lean','ChargeConsumer.lean','ChargeControls.lean','ConsumerSentinel.lean','ChargeQueries.lean']]
    negative=[BASE/n for n in ['NegativeToll.lean','NegativeUnused.lean','NegativeCollapse.lean','NegativeMerge.lean','MalformedImport.lean']]
    pins={}
    for src in mods+negative:
        shutil.copy2(src,SNAP/src.name)
        pins[str(src.relative_to(ROOT))]=hashlib.sha256(src.read_bytes()).hexdigest()
    receipt['source_pins']=pins
    receipt['tool_version']=run('lean-version',[str(ROOT/'bootloops-lean'),'--version']).stdout.strip()
    assert 'version 4.35.0' in receipt['tool_version']
    for src in mods:
        p=run(src.stem,[str(ROOT/'bootloops-lean'),'-o',str(SNAP/src.with_suffix('.olean').name),str(SNAP/src.name)])
        assert p.returncode==0,p.stdout
        assert 'sorryAx' not in p.stdout,p.stdout
    query=(LOG/'ChargeQueries.log').read_text()
    expected=['covered_balance','weight_unique','count_balance','close_balance','charge_budget','four_charges',
              'weight_eq_filter_length','selected_family_cost','parent_family_cost','projected_root_spec',
              'conditional_family_costs','conditional_family_count']
    allowed={'propext','Classical.choice','Quot.sound'}
    ax=[]
    for line in query.splitlines():
        if 'depends on axioms:' in line:
            names=set(re.search(r'\[(.*)\]',line).group(1).split(', '))
            assert names <= allowed,line
            ax.append(line)
    assert len(ax)==len(expected),(len(ax),expected)
    for name in expected:
        assert any(f".{name}' depends on axioms:" in line for line in ax),name
    receipt['axiom_queries']=ax
    for src in negative[:-1]:
        p=run(src.stem,[str(ROOT/'bootloops-lean'),str(SNAP/src.name)])
        assert p.returncode!=0,p.stdout
        assert 'Tactic `decide` proved that the proposition' in p.stdout and 'is false' in p.stdout,p.stdout
        assert 'unknown module' not in p.stdout and 'unknownIdentifier' not in p.stdout,p.stdout
    src=negative[-1]
    p=run(src.stem,[str(ROOT/'bootloops-lean'),str(SNAP/src.name)])
    assert p.returncode!=0 and 'NoSuchChargeModule' in p.stdout,p.stdout
    assert 'Tactic `decide` proved that the proposition' not in p.stdout,p.stdout
    receipt.update(grade='CLOSED-UNVERIFIED-CONDITIONAL-COUNT-COST',
        positive_numerical=8,wrong_output_clean_twins=8,malformed_inputs=4,
        false_proposition_rejections=4,malformed_import='separate-infrastructure-control',
        actual_family_sentinel='consumerT1; repeated leaf value 7; parent cost 2, child costs 0,0',
        remaining='Fresh nonauthor review; actual geometric restriction, support recovery, normalized transport, full G2 remain outside this arm.',
        numerical_receipt=str(cresult.relative_to(ROOT)))
except BaseException as e:
    receipt['grade']='FAILED-REPLAY'
    receipt['error']=repr(e)
    raise
finally:
    receipt['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    receipt['replay_source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    RESULT.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'receipt':str(RESULT.relative_to(ROOT)),'grade':receipt['grade']}),flush=True)
