#!/usr/bin/env python3
"""One-shot pre-candidate graph transport/mutation controls; no source reuse."""
import datetime,json,pathlib,time
from graph_controls_v1 import Graph,canonical,labels,proper,agrees,cleanup,cost,ready,coalesce,contract_block,expand_block,compare_record,disjoint
HERE=pathlib.Path(__file__).resolve().parent

def expand_tree(t,a,b,z):
    G=Graph(t)
    if not G.child: return None
    def emit(v):
        if v in G.taxon: return [a,b] if G.taxon[v]==z else G.taxon[v]
        return [emit(c) for c in G.child[v]]
    return emit(())

def main():
    start=time.perf_counter(); spec=json.loads((HERE/'TRANSPORT-EXPECTATIONS-v1.json').read_text()); base=json.loads((HERE/'EXPECTATIONS-v1.json').read_text()); rows=[]
    for f in base['fixtures']:
        if f['ready']:
            a,b,z=[f[k] for k in ('a','b','z')]
            T2=Graph(f['T']).contracted(a,b,z); ss2=[Graph(s).contracted(a,b,z) for s in f['ss']]
            T3=expand_tree(T2,a,b,z); ss3=[expand_tree(s,a,b,z) for s in ss2]
            compare_record(canonical(T3),canonical(f['T'])); compare_record([canonical(s) for s in ss3],[canonical(s) for s in f['ss']]); compare_record(sorted(labels(T3)),sorted(labels(f['T'])))
            rows.append({'id':f['id'],'targetRoundtrip':True,'sourceRoundtripCount':len(ss3),'originalTarget':f['T'],'expandedTarget':T3})
    s=spec['sequence']; T,ss,F=cleanup(s['T'],s['ss'],s['F'],s['singleton']); compare_record({'T':T,'ss':ss,'F':F,'cost':cost(ss,F)},s['cleanup'])
    a,b,z=[s[k] for k in ('a','b','z')]; T2=Graph(T).contracted(a,b,z); ss2=[Graph(t).contracted(a,b,z) for t in ss]; F2=[contract_block(B,a,b,z) for B in F]
    compare_record({'T':T2,'ss':ss2,'F':F2,'cost':cost(ss2,F2)},s['contract'])
    T3=expand_tree(T2,a,b,z); ss3=[expand_tree(t,a,b,z) for t in ss2]; F3=[expand_block(B,a,b,z) for B in F2]
    compare_record({'T':T3,'ss':ss3,'F':F3,'cost':cost(ss3,F3)},s['expand'])
    F4=F3+[[s['singleton']]]; compare_record(F4,s['reconstructedF']); assert agrees(s['T'],s['ss'],F4); compare_record(cost(s['ss'],F4),s['reconstructedCost'])
    null=spec['emptyNull']; compare_record(agrees(null['T'],null['ss'],null['F']),null['valid']); compare_record(cost(null['ss'],null['F']),null['cost'])
    E=spec['mutationExpected']; catches=[]
    def twin(name,clean,corrupt):
        compare_record(clean,E[name])
        try: compare_record(corrupt,E[name])
        except AssertionError as e: catches.append({'id':name,'clean':clean,'corrupt':corrupt,'expected':E[name],'caught':True,'finding':str(e)})
        else: raise AssertionError('surviving mutation '+name)
    hull=sorted(''.join(map(str,v)) for v in Graph([[[0,1],2],3]).hull([0,2])); twin('hull-unary-erasure',hull,[v for v in hull if v!='00'])
    twin('source-cost-minus-one',cost([[0,1],2],[[0,1],[2]]),len([[0,1],[2]])-1)
    twin('omit-reverse-direction',['forward','reverse'],['forward'])
    twin('fabricated-reconstruction',agrees(0,[0],[[0]]),agrees(0,[0],[]))
    twin('missing-component-readiness',ready([0,1],[0,1],0,1,2),Graph([0,1]).cherry_parent(0,1) is not None)
    twin('accept-nonfresh-z',ready([0,1],[[0,1]],0,1,1),proper([0,1],[[0,1]]) and Graph([0,1]).cherry_parent(0,1) is not None)
    twin('drop-surviving-label',labels(Graph([[0,1],2]).contracted(0,1,3)),[3])
    twin('weak-endpoint-clearance',disjoint([0,1],[[0,1],[1]]),disjoint([0,1],[[0],[1]]))
    F=[[0],[1]]; twin('reassignment-cost-equality',cost([[0,1]],coalesce(F,0,1))==cost([[0,1]],F),True)
    twin('duplicate-state-labels',proper([0,0],[0,0]),True)
    compare_record(len(catches),10)
    result={'status':'CONTROLS-PASS','startedUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'roundtripCount':len(rows),'roundtrips':rows,'sequence':s,'null':null,'mutations':catches,'seconds':time.perf_counter()-start}
    (HERE/'transport-mutations-v1.json').write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps({'status':result['status'],'roundtrips':len(rows),'mutationsCaught':len(catches),'seconds':result['seconds']}))
if __name__=='__main__': main()
