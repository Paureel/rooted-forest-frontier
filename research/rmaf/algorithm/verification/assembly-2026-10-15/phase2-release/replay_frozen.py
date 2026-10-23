"""Replay the unchanged prerelease mathematics with actual Lean outputs.

Only the driver's physical HERE and receipt destination are changed in a copy.
Its input expectations/checks are unchanged. The generator is replaced by an
exact table of actual compiled readouts; unknown calls fail (no model fallback).
"""
import sys,json,copy,importlib.util
from rebuild import ROOT,HERE,digest
from readout import I,C

def key(t,colors,q):return json.dumps([t,sorted((int(k),v) for k,v in colors.items()),q],separators=(',',':'))

def load_module(name,path):
    s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def main():
    pre=HERE.parent;receipt=ROOT/'research/rmaf/results/algorithm-assembly-fresh-review-actual-readout-v1.json'
    actual=json.loads(receipt.read_text())['actual'];cache={};used=[]
    for M in C['macros']:
        for call in M['calls']:
            colors=actual['COLOR:'+M['id']+':'+call['id']]
            cache[key(M['source'],colors,M['q'])]=actual['CALL:'+M['id']+':'+call['id']]
            if M['id']=='two-joint-diagonal':cache[key(M['source'],colors,3)]=actual['Q3:'+M['id']+':'+call['id']]
    E=C['clearing_not_final_agreement']
    colors,_=I.tagged_colors(E['source'],E['target'],E['parents'],E['v'],None,E['modes'])
    cache[key(E['source'],colors,E['q'])]=actual['CLEAR-NOT-AGREE:outputs']
    def actual_generate(t,colors,q):
        k=key(t,colors,q);assert k in cache,('no actual readout for frozen call',k)
        used.append(k);return {'outputs':copy.deepcopy(cache[k])}
    previous=I.base.generate;I.base.generate=actual_generate;sys.modules['instrument']=I
    records=[]
    for name,stage in [('run_controls','full'),('run_addendum',None)]:
        original=(pre/(name+'.py')).read_text()
        source=original.replace('HERE=Path(__file__).resolve().parent',f'HERE=Path({str(pre)!r})')
        source=source.replace('algorithm-assembly-prerelease-review-','algorithm-assembly-fresh-review-actual-replay-')
        assert source!=original
        target=HERE/(name+'-actual-copy.py');target.write_text(source)
        module=load_module('frozen_'+name,target)
        sys.argv=[str(target)]+(['--stage',stage] if stage else [])
        module.main()
        records.append({'source':str((pre/(name+'.py')).relative_to(ROOT)),
          'source_sha256':digest(pre/(name+'.py')),'copy':str(target.relative_to(ROOT)),
          'copy_sha256':digest(target),'edits':['physical HERE path only','new receipt destination prefix only'],
          'all_expectations_and_mathematical_checks_unchanged':True})
    I.base.generate=previous
    report={'status':'PASS_COMPLETE_FROZEN_BATTERY_USING_ACTUAL_LEAN_OUTPUTS',
      'actual_readout_receipt':str(receipt.relative_to(ROOT)),'actual_readout_sha256':digest(receipt),
      'copies':records,'actual_generator_calls_used':len(used),'actual_cached_calls':len(cache),
      'unknown_call_fallbacks':0,'replication_count_added':0}
    (ROOT/'research/rmaf/results/algorithm-assembly-fresh-review-frozen-replay-bridge-v1.json').write_text(json.dumps(report,indent=2)+'\n')
    print(report['status'],len(used),'actual-output uses; all207/52 full +addendum checks unchanged')

if __name__=='__main__':main()
