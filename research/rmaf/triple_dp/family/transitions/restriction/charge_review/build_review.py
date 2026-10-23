"""One-off independent source rebuild. Never invokes producer checkers/builds.
Known answers: exact theorem names, dependency sets, and false/correct twins.
Fail if names, dependencies, diagnostics, source pins or clean twins differ.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[7]
REVIEW = Path(__file__).resolve().parent
ROUTE = REVIEW.parent / 'charge_route'
RECEIPT = ROOT / 'research/rmaf/results/triple-family-transitions-restriction-charge-replay-final-v1.json'
FRESH = REVIEW / 'fresh-lean-v1'
LOGS = REVIEW / 'lean-logs-v1'
FRESH.mkdir()
LOGS.mkdir()

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

receipt = json.loads(RECEIPT.read_text())
pins = receipt['source_pins']
for path, wanted in pins.items():
    source = ROOT / path
    assert sha(source) == wanted, (path, 'producer source pin mismatch')
    shutil.copyfile(source, FRESH / source.name)
assert not list(FRESH.glob('*.olean'))
(FRESH / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
env = dict(os.environ, ELAN_HOME=str(ROOT / '.runtime/elan'), LEAN_PATH=str(FRESH))
rows = []
def run(name, args, expected_exit):
    start = time.monotonic()
    p = subprocess.run([str(ROOT / 'bootloops-lean'), *args], cwd=FRESH, env=env, text=True, capture_output=True, timeout=30)
    elapsed = time.monotonic()-start
    log = LOGS / (name+'.log')
    log.write_text(p.stdout+p.stderr)
    row = {'name':name,'exit':p.returncode,'expected_exit':expected_exit,'seconds':elapsed,'log':str(log.relative_to(ROOT)),'log_sha256':sha(log)}
    rows.append(row)
    assert p.returncode == expected_exit, row
    return p.stdout+p.stderr

version = run('lean-version',['--version'],0).strip()
assert 'version 4.35.0,' in version
modules = ['TripleDP','ConnectedRegions','FamilyAssembly','ChargeCore','ChargeConsumer','ChargeControls','ConsumerSentinel','ChargeQueries']
for name in modules:
    out=run(name,['-o',name+'.olean',name+'.lean'],0)
    assert 'sorryAx' not in out and 'error:' not in out

names = ['covered_balance','weight_unique','count_balance','close_balance','charge_budget','four_charges','weight_eq_filter_length','selected_family_cost','parent_family_cost','projected_root_spec','conditional_family_costs','conditional_family_count']
expected = {n:['propext','Classical.choice','Quot.sound'] for n in names}
expected['covered_balance']=['propext','Quot.sound']
expected['weight_eq_filter_length']=['propext']
expected['projected_root_spec']=['propext']
# Query all twelve exact types independently, including the two types absent
# from the producer query module's #check list.
query='import ChargeConsumer\nopen TripleDP.RestrictionCharge\n'+'\n'.join('#check '+n+'\n#print axioms '+n for n in names)+'\n'
(FRESH/'ReviewerQueries.lean').write_text(query)
qout=run('ReviewerQueries',['-o','ReviewerQueries.olean','ReviewerQueries.lean'],0)
found={n.split('.')[-1]:[x.strip() for x in ax.split(',')] for n,ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",qout)}
assert found==expected, found
assert len(re.findall(r'^TripleDP.RestrictionCharge\.',qout,re.M))==12
sentinel=(LOGS/'ConsumerSentinel.log').read_text()
assert "'TripleDP.RestrictionCharge.Sentinel.consumerT1' depends on axioms: [propext, Classical.choice, Quot.sound]" in sentinel

changes = {'NegativeToll':('= 0 :=','= 2 :='),'NegativeUnused':('= 1 :=','= 2 :='),'NegativeCollapse':('= 1 :=','= 2 :='),'NegativeMerge':('([0] : List Nat).length =','([0] : List Nat).length + 1 =')}
negatives=[]
for name,(bad,good) in changes.items():
    source=(FRESH/(name+'.lean')).read_text()
    assert source.count(bad)==1
    twin=name+'CleanTwin'
    (FRESH/(twin+'.lean')).write_text(source.replace(bad,good))
    clean=run(twin,['-o',twin+'.olean',twin+'.lean'],0)
    out=run(name,[name+'.lean'],1)
    assert 'Tactic `decide` proved that the proposition' in out and 'is false' in out, out
    assert 'unknown module' not in out and 'unknown constant' not in out
    negatives.append({'name':name,'diagnostic':out.strip(),'clean_twin':twin,'clean_twin_sha256':sha(FRESH/(twin+'.lean'))})
malformed=run('MalformedImport',['MalformedImport.lean'],1)
assert 'NoSuchChargeModule' in malformed and 'unknown module prefix' in malformed
assert 'Tactic `decide`' not in malformed
for path,wanted in pins.items():
    assert sha(ROOT/path)==wanted
report={'version':version,'fresh_path':str(FRESH.relative_to(ROOT)),'preexisting_olean_count':0,'producer_receipt_sha256':sha(RECEIPT),'source_pins':pins,'rows':rows,'exact_twelve_queries':names,'axiom_sets':found,'consumerT1_axioms':['propext','Classical.choice','Quot.sound'],'false_claims':negatives,'malformed_import':{'separate_infrastructure_control':True,'diagnostic':malformed.strip()},'pass':True}
(REVIEW/'lean-review-v1.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'pass':True,'commands':len(rows),'axiom_queries':len(found),'false_claims':len(negatives),'first_dependency_seconds':rows[1]['seconds'],'total_command_seconds':sum(r['seconds'] for r in rows)},indent=2))
