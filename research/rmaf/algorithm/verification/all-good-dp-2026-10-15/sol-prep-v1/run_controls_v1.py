#!/usr/bin/env python3
"""One-shot known-answer all-good preparation controls; candidate remains barred."""
import argparse,ast,collections,datetime,hashlib,json,pathlib,time
import agreement_oracle_v1 as O
import dp_runtime_v1 as D
from original_graph_v1 import Graph,canonical
H=pathlib.Path(__file__).resolve().parent

def exact(got,want,label):
    if got!=want:raise AssertionError({'check':label,'got':got,'expected':want})
def normalized_minima(Fs):return sorted(O.normalize_forest(F) for F in Fs)
def candidate_gate(f,result,oracle):
    exact(result['accepted'],f['allGood'],f['id']+' acceptance')
    if not f['allGood']:
        exact(result['minimum'],None,'guard refusal has no returned minimum');return
    exact(result['minimum'],f['oracleMinimum'],'runtime minimum')
    assert O.agrees(f['T'],f['ss'],result['F']),('runtime agreement',f['id'],result)
    exact(O.raw_cost(f['ss'],result['F']),result['minimum'],'nontruncated source offset')
    assert O.normalize_forest(result['F']) in oracle['minima']
    for key in ['visits','rows','evaluations','changes']:exact(result[key],f[key],f['id']+' '+key)
    exact(len(result['regions']),f['regions'],'region denominator')
    assert all(r['leaves'] for r in result['regions'])
    exact(sum(len(r['vertices']) for r in result['regions']),len(Graph(f['T']).child),'all original vertices retained')
    flat=sorted(x for B in result['F'] for x in B);exact(flat,sorted(O.labels(f['T'])),'leaf multiplicities')
    owner=D.owners(f['T'],f['ss']);exact(result['ownerMap'],{str(x):c for x,c in owner.items()},'unique actual source owners')
    for v,rs in result['internalRows'].items():exact(sorted(map(int,rs)),list(range(len(f['ss']))),'all owner colors in internal row')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--pilot',action='store_true');ap.add_argument('--out',required=True);a=ap.parse_args();spec=json.loads((H/'EXPECTATIONS-v1.json').read_text());controls=json.loads((H/'CONTROL-EXPECTATIONS-v1.json').read_text());start=time.perf_counter()
    expected_hashes=json.loads((H/'INSTRUMENTS-MANIFEST-v1.json').read_text())['files']
    for r in expected_hashes:exact(hashlib.sha256((H/r['path']).read_bytes()).hexdigest(),r['sha256'],'pre-execution source pin '+r['path'])
    ids=set(spec['plan']['pilotFixtureIds']);fixtures=[f for f in spec['fixtures'] if not a.pilot or f['id'] in ids];rows=[];observed={};oracles={}
    for f in fixtures:
        t=time.perf_counter();T,ss=f['T'],f['ss'];exact(O.proper(T,ss),f['proper'],'proper');exact(D.proper(T,ss),f['proper'],'runtime proper');exact(D.all_good(T,ss),f['allGood'],'all-good guard')
        oracle=O.summarize(T,ss);exact(oracle['minimum'],f['oracleMinimum'],'all-agreement minimum');exact(normalized_minima(oracle['minima']),normalized_minima(f['minima']),'every minimum witness')
        if f['proper']:exact(oracle['partitionCount'],{0:1,1:1,2:2,3:5,4:15}[len(O.labels(T))],'Bell denominator')
        result=D.run(T,ss);candidate_gate(f,result,oracle)
        if f['id'] in spec['internalRows']:exact(result['internalRows'],spec['internalRows'][f['id']],'literal row costs')
        oq=[oracle['minimum'] is not None and oracle['minimum']<=q for q in spec['q']];dq=[result['minimum']<=q for q in spec['q']] if result['accepted'] else None
        if result['accepted']:exact(dq,oq,'all sampled budget decisions')
        row={'id':f['id'],'oracle':oracle,'runtime':result,'oracleDecision':oq,'runtimeDecision':dq,'seconds':time.perf_counter()-t};rows.append(row);observed[f['id']]=result;oracles[f['id']]=oracle
    catches=[];raw=None
    if not a.pilot:
        byid={f['id']:f for f in fixtures}
        for e in spec['explicitForests']:
            f=byid[e['fixture']];F=e['F'];exact(O.agrees(f['T'],f['ss'],F),e['valid'],'explicit forest agreement');exact(O.raw_cost(f['ss'],F),e['rawCost'],'explicit raw offset')
            if 'targetHullsDisjoint' in e:exact(O.disjoint(f['T'],F),e['targetHullsDisjoint'],'global target hull control')
            if 'minimum' in e:exact(e['valid'] and e['rawCost']==oracles[f['id']]['minimum'],e['minimum'],'valid versus minimum')
            if 'refines' in e:exact(all(any(set(B)<=set(O.labels(s)) for s in f['ss']) for B in F),e['refines'],'refinement')
            if 'componentTopologyChecks' in e:
                checks=all(canonical(Graph(f['T']).restriction(B))==canonical(Graph(s).restriction(B)) for B in F for s in f['ss'] if set(B)<=set(O.labels(s)))
                exact(checks,e['componentTopologyChecks'],'component topology separately')
        for g in spec['geometry']:
            T=byid[g['fixture']]['T'];G=Graph(T);exact(sorted(D.addr(v) for v in G.hull(g['B'])),g['hull'],'original hull literal');exact(G.restriction(g['B']),g['restriction'],'suppressed topology literal')
        e=spec['leaflessRawControl'];f=byid[e['fixture']];G=Graph(f['T']);assignment={tuple(map(int,v)):c for v,c in e['assignment'].items()};rs=D.regions(G,assignment);changes=sum(assignment[v]!=assignment[w] for v,cs in G.child.items() for w in cs)
        exact(rs,e['regions'],'raw regions');exact(changes,e['changes'],'raw changes');exact(len(rs),e['regionCount'],'raw region count');exact(sum(not r['leaves'] for r in rs),e['leaflessRegions'],'leafless raw count');exact(sum(len(r['vertices']) for r in rs),e['vertexCount'],'raw vertex count')
        dropped=sorted(r['leaves'] for r in rs if r['leaves']);exact(dropped,e['droppedForest'],'dropped forest');exact(O.agrees(f['T'],f['ss'],dropped),e['droppedForestValid'],'dropped forest can be valid');exact(O.raw_cost(f['ss'],dropped),e['droppedForestCost'],'dropped cost');exact(len(rs)-len(f['ss']),e['rawRegionOffset'],'raw source offset');raw={'regions':rs,'changes':changes,'droppedForest':dropped}
        E=controls['semanticExpected']
        def twin(name,good,bad):
            exact(good,E[name],name+' clean')
            try:exact(bad,E[name],name+' corrupt')
            except AssertionError as er:catches.append({'id':name,'caught':True,'clean':good,'corrupt':bad,'finding':str(er)})
            else:raise AssertionError('survived '+name)
        cross=byid['balanced-cross'];clade=byid['balanced-clades'];mix=observed['balanced-mixed'];whole=[[0,2],[1,3]]
        twin('exclude-overlapping-current-hulls',D.all_good(cross['T'],cross['ss']),D.all_good(cross['T'],cross['ss']) and O.disjoint(cross['T'],[O.labels(s) for s in cross['ss']]))
        bad=byid['bad-whole-topology'];twin('ignore-full-source-topology',D.all_good(bad['T'],bad['ss']),D.proper(bad['T'],bad['ss']))
        r=observed['balanced-clades'];twin('wrong-source-count-subtraction',r['minimum'],len(r['F'])-1)
        owners=dict(r['ownerMap']);badowners={**owners,'3':0};twin('wrong-owner-map',owners,badowners)
        cs=sorted(map(int,observed['balanced-cross']['internalRows']['']));twin('missing-row-color',cs,cs[:-1])
        mc=mix['internalRows'][''];twin('drop-minimizing-root-color',min(mc.values()),min(v for c,v in mc.items() if c!='2'))
        twin('drop-leafless-vertices',sum(len(r['vertices']) for r in rs),sum(len(r['vertices']) for r in rs if r['leaves']))
        twin('drop-leafless-region-count',len(rs),sum(bool(r['leaves']) for r in rs))
        twin('ignore-global-target-hull-overlap',O.agrees(cross['T'],cross['ss'],whole),all(canonical(Graph(cross['T']).restriction(O.labels(s)))==canonical(s) for s in cross['ss']))
        singles=[[0],[1],[2],[3]];valid=O.agrees(cross['T'],cross['ss'],singles);twin('accept-valid-nonminimum-forest',valid and O.raw_cost(cross['ss'],singles)==oracles['balanced-cross']['minimum'],valid)
        invalid=[[0,1,2,3]];twin('truncate-invalid-negative-offset',O.agrees(cross['T'],cross['ss'],invalid) and O.raw_cost(cross['ss'],invalid)<=0,max(0,O.raw_cost(cross['ss'],invalid))<=0)
        twin('false-budget-zero',observed['balanced-cross']['minimum']<=0,D.all_good(cross['T'],cross['ss']))
        exact(len(catches),controls['semanticCorruptionCount'],'semantic catch denominator')
        exact(D.POISON_CALLS,{'unknown_minimum':0,'partition_oracle':0},'runtime never touched poisoned backends')
        # Same runtime call adapter for clean implementation and poisoned corrupt wrappers.
        original=D.run
        for backend in ['unknown_minimum','partition_oracle']:
            def corrupt(T,ss,backend=backend):return getattr(D,backend)(T,ss)
            D.run=corrupt
            try:
                try: D.run(cross['T'],cross['ss'])
                except D.ForbiddenOracleAccess as er:catches.append({'id':backend+'-access','caught':True,'finding':str(er)})
                else:raise AssertionError('poison failed '+backend)
            finally:D.run=original
        exact(len(catches),controls['semanticCorruptionCount']+controls['poisonCorruptionCount'],'all catch denominator')
        module=ast.parse((H/'dp_runtime_v1.py').read_text());imports=[node.module for node in ast.walk(module) if isinstance(node,ast.ImportFrom)];assert 'agreement_oracle_v1' not in imports
        assert 'partitions(' not in (H/'dp_runtime_v1.py').read_text() and 'summarize(' not in (H/'dp_runtime_v1.py').read_text()
    result={'status':'PRE-CANDIDATE-CONTROLS-PASS','phase':'pilot' if a.pilot else 'fixed','emissionUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'fixtureCount':len(rows),'expectedFixtureCount':len(fixtures),'rows':rows,'catches':catches,'leaflessRaw':raw,'seconds':time.perf_counter()-start,'independentReplicaIncrement':0,'candidateContact':False}
    exact(len(rows),len(fixtures),'fixture denominator');pathlib.Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'phase':result['phase'],'fixtures':len(rows),'corruptionsCaught':len(catches),'seconds':result['seconds']}))
if __name__=='__main__':main()
