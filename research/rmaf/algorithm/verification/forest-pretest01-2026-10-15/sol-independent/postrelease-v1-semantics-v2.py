#!/usr/bin/env python3
"""Replay frozen independent hand controls on the actual released entry point.
Expected predicates/forests come only from the frozen fresh graph instrument,
not author fixtures/results. No large census.
"""
import argparse
import collections
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
import traceback

HERE=Path(__file__).resolve().parent
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience')
BUILD=HERE/'postrelease-v1-scientific'
LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
spec=importlib.util.spec_from_file_location('fresh_graph_controls',HERE/'graph_controls-v1.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)

def require(c,m):
    if not c:raise AssertionError(m)

def lean_tree(t):
    return f'(.leaf {t})' if type(t) is int else f'(.node {lean_tree(t[0])} {lean_tree(t[1])})'

def fixtures():
    base=json.loads((HERE/'fixtures-v1.json').read_text())['cases']
    out=[(c['id']+':base',c['T'],c['ss']) for c in base]
    for c in base:
        if c['proper']:
            out.append((c['id']+':mirror_permute',None if c['T'] is None else g.mirror(c['T']),
                        [g.mirror(s) for s in reversed(c['ss'])]))
            out.append((c['id']+':large_nat',None if c['T'] is None else g.relabel(c['T']),
                        [g.relabel(s) for s in c['ss']]))
    return out

def generate(cases,name):
    text=['import ForestPretestWork','open Lean RMAF ForestState ForestPretest01',
          'set_option maxRecDepth 100000',
          'def encodeIndependentResult : Result → Json',
          '  | .refused => Json.mkObj [("kind",toJson "refused")]',
          '  | .rejected => Json.mkObj [("kind",toJson "rejected")]',
          '  | .found F => Json.mkObj [("kind",toJson "found"),("forest",toJson F)]']
    inputs=[]
    for i,(label,T,ss) in enumerate(cases):
        universe=[] if T is None else g.b_leaves(T)
        partitions=list(g.b_partitions(universe))
        # Also check literal block/label-order permutations through agrees.
        partitions+= [[list(reversed(b)) for b in reversed(p)] for p in partitions]
        inputs.append(partitions)
        t='none' if T is None else '(some '+lean_tree(T)+')'
        s='['+','.join(lean_tree(u) for u in ss)+']'
        p=json.dumps(partitions,separators=(',',':'))
        text.extend([f'def independentT{i} : Option Tree := {t}',
                     f'def independentS{i} : List Tree := {s}',
                     f'def independentP{i} : List (List (List Nat)) := {p}',
                     '#eval IO.println ("SEMANTIC " ++ (Json.mkObj [',
                     f'  ("id",toJson {json.dumps(label)}),',
                     f'  ("proper",toJson (proper independentT{i} independentS{i})),',
                     f'  ("result",encodeIndependentResult (pretest01 independentT{i} independentS{i})),',
                     f'  ("candidates",toJson (candidates independentS{i})),',
                     f'  ("candidate_valid",toJson ((candidates independentS{i}).map (agrees independentT{i} independentS{i}))),',
                     f'  ("candidate_cost",toJson ((candidates independentS{i}).map (additionalCost independentS{i}))),',
                     f'  ("partition_valid",toJson (independentP{i}.map (agrees independentT{i} independentS{i})))',
                     ']).compress)'])
    source=BUILD/(name+'.lean');source.write_text('\n'.join(text)+'\n')
    return source,inputs

def compare(cases,parts,rows):
    require(len(rows)==len(cases),'actual replay denominator')
    result=[]
    for (label,T,ss),partitions,actual in zip(cases,parts,rows):
        require(actual['id']==label,'row identity')
        proper=g.a_proper(T,ss)
        require(proper==g.b_proper(T,ss)==actual['proper'],label+':proper')
        expected=[p for _,p in g.a_candidates(ss)]
        require(len(expected)==len(actual['candidates']),label+':candidate count for every tree')
        if proper:
            require(collections.Counter(map(g.canon,expected))==collections.Counter(map(g.canon,actual['candidates'])),label+':proper candidate multiset')
        require(len(actual['candidates'])==len(actual['candidate_valid'])==len(actual['candidate_cost']),label+':candidate arrays')
        for p,valid,cost in zip(actual['candidates'],actual['candidate_valid'],actual['candidate_cost']):
            require(valid==g.a_valid(T,ss,p)==g.b_valid(T,ss,p),label+':full candidate predicate')
            require(cost==max(0,len(p)-len(ss)),label+':prepaid cost')
        validity=[]
        for p in partitions:
            a,b=g.a_valid(T,ss,p),g.b_valid(T,ss,p)
            require(a==b,label+':independent validator routes')
            validity.append(b)
        require(validity==actual['partition_valid'],label+':every frozen small partition predicate')
        minimum=min((max(0,len(p)-len(ss)) for p,v in zip(partitions,validity) if v),default=None)
        decision='refused' if not proper else 'found' if minimum<=1 else 'rejected'
        require(actual['result']['kind']==decision,label+':actual production decision')
        if decision=='found':
            forest=actual['result']['forest']
            require(g.b_valid(T,ss,forest) and len(forest)-len(ss)==minimum,label+':actual global finite minimum')
        result.append({'id':label,'decision':decision,'minimum':minimum,'candidate_entries':len(expected),
                       'partition_checks':len(partitions),'pass':True})
    return result

def main():
    p=argparse.ArgumentParser();p.add_argument('--pilot',action='store_true');p.add_argument('--out',required=True)
    a=p.parse_args();out=Path(a.out);require(not out.exists(),'refuse evidence overwrite')
    start=time.perf_counter();result={'pilot':a.pilot,'rows':[],'disk_free_before':shutil.disk_usage(HERE).free}
    try:
        require(result['disk_free_before']>=3*2**30,'disk floor')
        cases=fixtures()
        if a.pilot:cases=[c for c in cases if c[0] in ('singleton:base','crossed_forest:base')]
        name='IndependentSemanticsPilotV2' if a.pilot else 'IndependentSemanticsFullV2'
        source,parts=generate(cases,name)
        environment=dict(os.environ);environment['LEAN_PATH']=str(BUILD)
        t=time.perf_counter()
        command=[str(LEAN),source.name]
        process=subprocess.run(command,cwd=BUILD,env=environment,text=True,capture_output=True,timeout=60)
        result['command']={'command':command,'seconds':time.perf_counter()-t,'timeout_seconds':60,
                           'exit_code':process.returncode,'stdout':process.stdout,'stderr':process.stderr,
                           'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
        require(process.returncode==0,'actual semantic replay compile/eval failed')
        rows=[json.loads(line[9:]) for line in process.stdout.splitlines() if line.startswith('SEMANTIC ')]
        result['rows']=compare(cases,parts,rows)
        result['partition_checks']=sum(r['partition_checks'] for r in result['rows'])
        result['candidate_entries']=sum(r['candidate_entries'] for r in result['rows'])
        result['status']='PASS'
    except BaseException:
        result['status']='FAIL';result['failure']=traceback.format_exc()
    finally:
        result['seconds']=time.perf_counter()-start;result['disk_free_after']=shutil.disk_usage(HERE).free
        out.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({k:result[k] for k in ('status','pilot','seconds','disk_free_after')}
                         | {'rows':len(result['rows']),'receipt':str(out)}))
    return 0 if result['status']=='PASS' else 1

if __name__=='__main__':raise SystemExit(main())
