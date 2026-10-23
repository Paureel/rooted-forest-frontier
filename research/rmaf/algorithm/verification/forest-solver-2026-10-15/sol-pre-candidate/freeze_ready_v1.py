#!/usr/bin/env python3
"""One-shot reproducible READY seal/check for this prerelease review only."""
import hashlib
import json
from pathlib import Path
import sys
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[5]
READY=HERE/'READY-v1.json'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def receipt(name):
    x=json.loads((HERE/name).read_text())
    assert x['passed'] is True, 'unpassed positive receipt '+name
    return x


def verify():
    data=json.loads(READY.read_text())
    for row in data['entries']:
        path=HERE/row['path']
        assert path.is_file(), 'missing payload '+row['path']
        assert path.stat().st_size==row['size'], 'size drift '+row['path']
        assert digest(path)==row['sha256'], 'hash drift '+row['path']
    assert len(data['entries'])==len({r['path'] for r in data['entries']}), 'duplicate READY payload'
    print(json.dumps({'status':'READY hash check passed','entries':len(data['entries']),
                      'READY_sha256':digest(READY),'candidate_release':'NOT GRANTED'}))


def seal():
    assert not READY.exists(), 'READY exists; never overwrite a frozen seal'
    plants=receipt('graph-plants-v2.json')
    assert len(plants['controls'])==17
    graph=receipt('graph-battery-v2.json')
    assert len(graph['cases'])==11 and len(graph['metamorphisms'])==12
    assert graph['partition_counts']['6']==203
    receipt('graph-pilot-v2.json')
    toy=receipt('toy-battery-v2.json')
    assert len(toy['gates'])==11 and len(toy['commands'])==12
    replacement=receipt('replacement-controls-v1.json')
    assert len(replacement['cases'])==2 and len(replacement['false_twins'])==7
    receipt('standard-axiom-control-v1.json')
    adapter=receipt('literal-adapter-control-v1.json')
    assert adapter['import_exact_records']['origins']==14
    null=receipt('raw-null-controls-v2.json')
    assert len(null['false_twins'])==4
    assert json.loads((HERE/'graph-plants-v1.json').read_text())['passed'] is False
    assert json.loads((HERE/'toy-battery-v1.json').read_text())['passed'] is False
    assert json.loads((HERE/'toy-pilot-v1.json').read_text())[-1]['returncode']==1
    assert json.loads((HERE/'raw-null-preparation-failure-v1.json').read_text())['passed'] is False
    ledger=json.loads((HERE/'CONTACT-LEDGER-v1.json').read_text())
    assert ledger['candidate_contacts']==[]
    files=sorted(p for p in HERE.rglob('*') if p.is_file()
                 and '__pycache__' not in p.parts and p!=READY)
    entries=[{'path':str(p.relative_to(HERE)),'size':p.stat().st_size,'sha256':digest(p)} for p in files]
    public_paths=[
      'research/rmaf/algorithm/verification/forest-solver-2026-10-15/TARGET-v1.md',
      'research/rmaf/lean/RMAF.lean',
      'research/rmaf/algorithm/universal233/state_reductions/State.lean',
      'research/rmaf/algorithm/universal233/forest_solver/TARGET-v1.md']
    data={'schema':'independent-prerelease-READY-v1','status':'READY; awaiting separate exact root release',
      'owner':'/root/sol_forest_solver_review','utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
      'candidate_contact_before_READY':False,'candidate_release':'NOT GRANTED',
      'scope':'finite prerelease controls and fresh origin audit toy qualification only',
      'candidate_required':{'manifest':'forest_solver/FOREST-SOLVER-MANIFEST-v3.json',
        'sha256':'89937a6f71bceb2dbeb64917b4b805e8f193fa485b00ec28acecdc95d047dcf5','payload_entries':540},
      'retained_failures':['graph v1 JSON diagnostic','Lean auditor v1 API qualification',
                           'toy battery v1 module/hygienic adapter mismatch','raw-null v1 parse typo'],
      'independence':'fresh code within same model family; no statistical independence or extra replication count',
      'excluded_transients':['__pycache__'],
      'public_source_bindings':[{'path':s,'sha256':digest(ROOT/s)} for s in public_paths],
      'entries':entries}
    READY.write_text(json.dumps(data,indent=2)+'\n')
    for p in files+[READY]: p.chmod(0o444)
    verify()


if __name__=='__main__':
    if sys.argv[1:] == ['seal']: seal()
    elif sys.argv[1:] == ['check']: verify()
    else: raise SystemExit('use seal (once) or check')
