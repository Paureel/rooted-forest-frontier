"""Re-execute the preregistered origin/axiom controls in a fresh owned folder."""
from pathlib import Path
import importlib.util,json,sys
sys.dont_write_bytecode=True
import rebuild as R

def main():
    source=R.HERE.parent/'toy_gates_v2.py';raw=source.read_text()
    copied=raw.replace('HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4]','HERE=Path(__file__).resolve().parent.parent;ROOT=HERE.parents[4]').replace("build=HERE/'toy-build-v2'","build=HERE/'phase2-release'/'toy-replay'").replace('algorithm-kept-parent-prerelease-toy-gates-v2.json','algorithm-kept-parent-fresh-review-toy-gates-v1.json')
    p=R.HERE/'ReplayToys.py';p.write_text(copied)
    spec=importlib.util.spec_from_file_location('fresh_replayed_origin_toys',p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);m.main()
    report={'status':'PASS_FROZEN_TOY_GATE_REPLAY','original_sha256':R.sha(source),'adapted_sha256':R.sha(p),'changes':'physical input root, fresh build folder and result filename only; source/false expectations unchanged','candidate_imports_in_toys':False}
    (R.HERE/'toy-replay-adapter.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
