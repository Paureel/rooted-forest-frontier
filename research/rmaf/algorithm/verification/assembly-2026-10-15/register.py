"""Register immutable expectations/instruments before first execution."""
from pathlib import Path
import hashlib,json,datetime

HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    own=[HERE/x for x in ['TARGET-v1.md','CONTROLS-v1.json','CONTACTS-v1.md','instrument.py',
      'run_controls.py','toy_axiom_gate.py','LATER-RELEASE-GATE.md','register.py']]
    sources=[ROOT/x for x in ['research/rmaf/algorithm/TARGET.md','research/rmaf/lean/RMAF.lean',
      'research/rmaf/algorithm/universal233/core/CoreProgram.lean',
      'research/rmaf/algorithm/universal233/core/CoreGraph.lean',
      'research/rmaf/algorithm/universal233/geometry/Geometry.lean',
      'research/rmaf/algorithm/universal233/geometry/Bridge.lean',
      'research/rmaf/algorithm/universal233/geometry/Composition.lean',
      'research/rmaf/algorithm/verification/core-completion-2026-10-15/frozen-v1/independent_instrument.py']]
    # Parsing the frozen data establishes syntax only, without running any
    # graph/agreement/generator/control calculation.
    json.loads((HERE/'CONTROLS-v1.json').read_text())
    rows=[{'path':str(p.relative_to(ROOT)),'realpath':str(p.resolve()),'sha256':sha(p),'bytes':p.stat().st_size} for p in own+sources]
    result={'stage':'PRE_CANDIDATE_EXPECTATION_INSTRUMENT_FREEZE','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'frozen_before_any_new_instrument_execution':True,'candidate_contact':False,
      'candidate_compilation':False,'replication_count_added':0,
      'before_execution_files':rows,'timing_plan':{'pilot':'three hard forest classifications and one clique call, small graph/receipt/root/label controls',
        'after_pilot':'only if measured small, full literal15hard partitions/9macro calls/namedforests and4toy gate modules; no broad census'},
      'all_main_milestones':'OPEN','release_requires':'exact final author manifests AND explicit root release after READY'}
    p=HERE/'FREEZE-v1.json';p.write_text(json.dumps(result,indent=2)+'\n')
    (HERE/'FREEZE-v1.sha256').write_text(sha(p)+'  FREEZE-v1.json\n')
    for f in own:
        if f.name!='TARGET-v1.md':f.chmod(0o444)
    p.chmod(0o444);(HERE/'FREEZE-v1.sha256').chmod(0o444)
    print('PREEXECUTION FROZEN',len(rows),'files',sha(p))

if __name__=='__main__':main()
