"""Replay unchanged frozen checks; every generator call must hit actual Lean cache."""
from copy import deepcopy
from pathlib import Path
import importlib.util,json,sys
sys.dont_write_bytecode=True
import rebuild as R
from readout import configkey

def main():
    pre=R.HERE.parent;src=pre/'run_controls_v2.py';raw=src.read_text()
    adapted=raw.replace('HERE=Path(__file__).resolve().parent; ROOT=I.ROOT','HERE=Path(__file__).resolve().parent.parent; ROOT=I.ROOT').replace('algorithm-kept-parent-prerelease-{mode}-v2.json','algorithm-kept-parent-fresh-review-replay-{mode}-v1.json')
    assert adapted!=raw
    copy=R.HERE/'ReplayFrozen.py';copy.write_text(adapted)
    sys.path.insert(0,str(pre))
    spec=importlib.util.spec_from_file_location('actual_replay_frozen',copy);M=importlib.util.module_from_spec(spec);spec.loader.exec_module(M)
    receipt=json.loads((R.ROOT/'research/rmaf/results/algorithm-kept-parent-fresh-review-readout-v1.json').read_text());cache=receipt['generate_cache'];old=M.I.graph.generate;calls=[]
    def actual_generate(t,colors,q):
        key=configkey(t,colors,q);assert key in cache,('UNFROZEN_ACTUAL_CALL',key)
        # Trace is a disclosed independent pointer diagnostic only. All raw
        # output occurrences, counters and refusals come from compiled Lean.
        trace=old(t,colors,q)['trace'];r=deepcopy(cache[key]);r['trace']=trace
        calls.append({'key':key,'actual_cache':True,'output_occurrences':len(r['outputs'])});return r
    M.I.graph.generate=actual_generate
    for mode in ('pilot','full'):
        sys.argv=[str(copy),mode];M.main()
    assert len(calls)==29, len(calls) # 8 pilot +20 full +duplicate-label refusal.
    result={'status':'PASS_UNCHANGED_FROZEN_BATTERY_ON_ACTUAL_LEAN','frozen_runner_sha256':R.sha(src),'adapted_runner_sha256':R.sha(copy),'changes':'physical input root and result filenames only; exact assertions/expectations unchanged','actual_generate_calls':len(calls),'calls':calls,'unknown_call_fallback':False,'trace_disclosure':'unchanged independent pointer trace only; all output/counter data actual Lean readout','all_main_milestones':'OPEN','replication_count_added':0}
    p=R.ROOT/'research/rmaf/results/algorithm-kept-parent-fresh-review-frozen-replay-v1.json';p.write_text(json.dumps(result,indent=2)+'\n');print(result['status'],len(calls))
if __name__=='__main__':main()
