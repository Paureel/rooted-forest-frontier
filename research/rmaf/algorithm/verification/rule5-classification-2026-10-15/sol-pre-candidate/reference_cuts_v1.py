#!/usr/bin/env python3
"""One-shot original-edge/union-find reference; no BFS/clade/project imports.

This computes exact catalogues for three fixed constructed tree pairs, not a
tree census or a recursive algorithm. Outputs become frozen literal references
before the separately implemented BFS/partition/clade comparator runs.
"""
from itertools import combinations
import hashlib
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
SPEC = json.loads((HERE/'FIXTURE-INPUTS-v1.json').read_text())
MODE = sys.argv[1]
RECEIPT = HERE/('reference-'+MODE+'-v1.json')
RESULT = {'candidate_contact':False,'route':'edge subsets/union-find/canonical nested shape',
          'context':'new original-address reference, shared public definitions/model; zero extra replication credit',
          'mode':MODE,'plants':[],'cases':[]}
DEADLINE = time.perf_counter()+30


def leaves(t):
    return [t] if type(t) is int else leaves(t[0])+leaves(t[1])


def restriction(t,labels):
    if type(t) is int:
        return t if t in labels else None
    left,right = restriction(t[0],labels),restriction(t[1],labels)
    if left is None:return right
    if right is None:return left
    return [left,right]


def canonical(t):
    if t is None:return None
    if type(t) is int:return ('leaf',t)
    a,b = canonical(t[0]),canonical(t[1])
    return ('node',*sorted([a,b]))


def key(forest):
    return tuple(sorted(tuple(sorted(block)) for block in forest))


def refines(forest,partition):
    return all(any(set(block)<=set(owner) for owner in partition) for block in forest)


def edge_partition_catalogue(t):
    # Integer vertex IDs and disjoint-set unions; no graph-path/hull computation.
    vertices=[];parents=[];taxa={}
    def collect(node,address,parent):
        i=len(vertices);vertices.append(address);parents.append(parent)
        if type(node) is int:
            taxa[i]=node
        else:
            collect(node[0],address+(0,),i);collect(node[1],address+(1,),i)
    collect(t,(),-1)
    assert len(set(taxa.values()))==len(taxa) and all(x>=0 for x in taxa.values())
    n=len(vertices);edges=tuple(range(1,n));catalogue={};attempts=0;leafless=0
    for number in range(len(taxa)):
        for cut_tuple in combinations(edges,number):
            attempts+=1;cut=set(cut_tuple);parent=list(range(n))
            if attempts % 4096 == 0 and time.perf_counter()>DEADLINE:
                raise TimeoutError('fixed reference run exceeded30s wall cap')
            def find(i):
                while parent[i]!=i:
                    parent[i]=parent[parent[i]];i=parent[i]
                return i
            for child in edges:
                if child not in cut:
                    parent[find(child)]=find(parents[child])
            blocks={}
            for i,label in taxa.items():blocks.setdefault(find(i),[]).append(label)
            if len(blocks)!=number+1:
                leafless+=1;continue
            forest=key(blocks.values())
            if forest not in catalogue:
                catalogue[forest]=[list(vertices[i]) for i in cut_tuple]
    return catalogue,{'vertices':n,'edges':len(edges),'attempted_cut_sets':attempts,
                      'leafless_cut_sets_rejected':leafless,'distinct_leaf_partitions':len(catalogue)}


def af_catalogue(T,S):
    target,tc=edge_partition_catalogue(T);source,sc=edge_partition_catalogue(S)
    result=[]
    for forest in sorted(target.keys() & source.keys(),key=lambda f:(len(f),f)):
        if all(canonical(restriction(T,set(B)))==canonical(restriction(S,set(B))) for B in forest):
            result.append({'F':[list(B) for B in forest],'sourceCuts':source[forest],
                           'targetCuts':target[forest],'originalCost':len(forest)-1})
    return result,{'target':tc,'source':sc}


def child_rows(case,forests):
    S=case['source'];labels=leaves(S)
    specs=[('hard-two',case['original_cuts'],case['partition'])]
    if case['expected_prefix']!='large':
        for x,y,name in [('p','a','p+a'),('p','b','p+b'),('q','a','q+a'),('q','b','q+b')]:
            a,b=case[x],case[y]
            Q=[[a],[b],[z for z in labels if z not in (a,b)]]
            specs.append((name,[case['terminal_arcs'][x],case['terminal_arcs'][y]],Q))
    rows=[]
    for name,cuts,Q in specs:
        assert len(cuts)==2 and len(Q)==3 and all(Q)
        compatible=[row for row in forests if refines(row['F'],Q)]
        minimum=min(len(row['F'])-len(Q) for row in compatible)
        rows.append({'id':name,'sourceCuts':cuts,'partition':Q,
          'sourceForest':[restriction(S,set(B)) for B in Q],'paid':2,
          'sourceCount':3,'minimumAdditionalCost':minimum,
          'compatibleAF':[row['F'] for row in compatible],
          'minimumForests':[row['F'] for row in compatible if len(row['F'])-3==minimum]})
    return rows


def case_reference(case):
    start=time.perf_counter();forests,work=af_catalogue(case['target'],case['source'])
    assert forests
    minimum=min(row['originalCost'] for row in forests)
    children=child_rows(case,forests)
    budgets=[]
    for q in range(minimum+2):
        calls=[{'child':r['id'],'remaining':q-2,'succeeds':r['minimumAdditionalCost']<=q-2}
               for r in children] if q>=2 else []
        budgets.append({'q':q,'originalSuccess':minimum<=q,'paidCalls':calls,
                        'anyChildSuccess':any(r['succeeds'] for r in calls)})
    return {'id':case['id'],'minimumOriginalCost':minimum,'originalAF':forests,
      'children':children,'budgetControls':budgets,'edgeEnumeration':work,
      'seconds':time.perf_counter()-start}


try:
    for name,plant in SPEC['reference_plants'].items():
        start=time.perf_counter();rows,work=af_catalogue(plant['target'],plant['source'])
        actual={key(r['F']) for r in rows};expected={key(F) for F in plant['AF']}
        assert actual==expected and min(r['originalCost'] for r in rows)==plant['minimum']
        bad=set(actual);bad.pop()
        try:assert bad==expected
        except AssertionError:caught=True
        else:raise AssertionError('missing AF false plant survived')
        RESULT['plants'].append({'id':name,'AF':len(rows),'seconds':time.perf_counter()-start,
                                 'missing_AF_caught':caught,'passed':True,'work':work})
    cases=[c for c in SPEC['cases'] if c['id']=='sizeTwo7'] if MODE=='pilot' else SPEC['cases']
    assert MODE in ('pilot','full')
    for case in cases:
        row=case_reference(case)
        path=HERE/('REFERENCE-'+case['id']+'-'+MODE+'-v1.json')
        path.write_text(json.dumps(row,indent=2)+'\n')
        RESULT['cases'].append({'id':case['id'],'path':path.name,'seconds':row['seconds'],
          'originalAF':len(row['originalAF']),'minimumOriginalCost':row['minimumOriginalCost'],
          'childMinima':[r['minimumAdditionalCost'] for r in row['children']],
          'edgeEnumeration':row['edgeEnumeration'],'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
        RECEIPT.write_text(json.dumps(RESULT,indent=2)+'\n')
    RESULT['passed']=True
except Exception as exc:
    RESULT['passed']=False;RESULT['failure']=repr(exc)
    raise
finally:
    RECEIPT.write_text(json.dumps(RESULT,indent=2)+'\n')
print(json.dumps({'passed':True,'mode':MODE,'plants':len(RESULT['plants']),
                  'cases':[{k:r[k] for k in ['id','seconds','originalAF','minimumOriginalCost','childMinima']} for r in RESULT['cases']]}))
