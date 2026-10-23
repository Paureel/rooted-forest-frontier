#!/usr/bin/env python3
"""One-campaign fresh MAF controls, two mathematical routes, no project imports.

Graph route enumerates edge deletions and reads leaf-bearing connected components.
Partition route enumerates set partitions and directly computes rooted restrictions
and original-tree minimal hulls. They share no validity, hull or restriction code.
Both are authored here, so their agreement is finite cross-method evidence only.
"""
import itertools, json, pathlib, sys, time

HERE=pathlib.Path(__file__).resolve().parent

def canon_blocks(blocks):
    return tuple(sorted(tuple(sorted(b)) for b in blocks))

def validate_input(a,b):
    def leaves(t):
        if type(t) is int and t>=0: return [t]
        if type(t) in (list,tuple) and len(t)==2: return leaves(t[0])+leaves(t[1])
        raise ValueError('not rooted binary Nat tree')
    x,y=leaves(a),leaves(b)
    if len(set(x))!=len(x) or len(set(y))!=len(y): raise ValueError('duplicate leaf')
    if set(x)!=set(y): raise ValueError('different leaf set')
    return tuple(sorted(x))

# ROUTE G: delete graph edges, orient components from the inherited root direction.
def graph_forests(tree):
    children={}; labels={}; edges=[]
    def add(t):
        i=len(children); children[i]=[]
        if type(t) is int and t>=0:
            if t in labels.values():raise ValueError('graph duplicate leaf')
            labels[i]=t
        elif type(t) in (list,tuple) and len(t)==2:
            for branch in t:
                # Reserve the edge before descending: explicit preorder edge bits.
                e=len(edges); edges.append(None)
                j=add(branch); edges[e]=(i,j); children[i].append(j)
        else:raise ValueError('graph tree is not binary Nat input')
        return i
    add(tree)
    edge_index={edge:i for i,edge in enumerate(edges)}
    forests={}
    for mask in range(1<<len(edges)):
        parent=list(range(len(children)))
        def root(v):
            while parent[v]!=v: v=parent[v]
            return v
        for bit,(u,v) in enumerate(edges):
            if not (mask>>bit)&1: parent[root(v)]=root(u)
        groups={}
        for v in children: groups.setdefault(root(v),[]).append(v)
        components=[]
        for verts in groups.values():
            selected=tuple(sorted(labels[v] for v in verts if v in labels))
            if not selected: continue
            vs=set(verts)
            top=next(v for v in verts if not any((u,v) in edge_index and u in vs for u in verts))
            def shape(v):
                if v in labels: return ('L',labels[v])
                pieces=[shape(w) for w in children[v] if w in vs]
                pieces=[x for x in pieces if x is not None]
                if len(pieces)==0: return None
                if len(pieces)==1: return pieces[0]
                return ('N',)+tuple(sorted(pieces))
            components.append((selected,shape(top)))
        key=tuple(sorted(components))
        forests[key]=min(mask,forests.get(key,mask))
    return forests,edges

def graph_agreements(a,b):
    ga,ea=graph_forests(a); gb,eb=graph_forests(b)
    al={label for block,_ in next(iter(ga)) for label in block}
    bl={label for block,_ in next(iter(gb)) for label in block}
    if al!=bl:raise ValueError('graph leaf sets differ')
    rows={tuple(x[0] for x in key):{'a_mask':ga[key],'b_mask':gb[key]} for key in ga.keys() & gb.keys()}
    return rows,{'a_edges':ea,'b_edges':eb}

# ROUTE P: direct set partitions, prune recursive tree and compute original hulls.
def partitions(items):
    if not items:
        yield (); return
    first=items[0]
    for rest in partitions(items[1:]):
        yield canon_blocks(((first,),)+rest)
        for i in range(len(rest)):
            yield canon_blocks(rest[:i]+(tuple(sorted((first,)+rest[i])),)+rest[i+1:])

def partition_valid(a,b,blocks):
    def collect(t):
        if type(t) is int: return [t]
        return collect(t[0])+collect(t[1])
    aa=collect(a); flat=[v for block in blocks for v in block]
    if any(len(block)==0 for block in blocks) or sorted(flat)!=sorted(aa) or len(set(flat))!=len(flat):
        return False
    def inspect(t,block):
        wanted=set(block)
        paths={}
        def restrict(node,path):
            if type(node) is int:
                if node in wanted: paths[node]=path; return ('L',node)
                return None
            left=restrict(node[0],path+(0,)); right=restrict(node[1],path+(1,))
            if left is None:return right
            if right is None:return left
            return ('N',)+tuple(sorted((left,right)))
        restricted=restrict(t,())
        if len(paths)==1: hull={next(iter(paths.values()))}
        else:
            pp=list(paths.values()); common=0
            while all(len(p)>common and p[common]==pp[0][common] for p in pp): common+=1
            hull={p[:i] for p in pp for i in range(common,len(p)+1)}
        return restricted,hull
    occupied_a=set(); occupied_b=set()
    for block in blocks:
        sa,ha=inspect(a,block); sb,hb=inspect(b,block)
        if sa!=sb or occupied_a & ha or occupied_b & hb:return False
        occupied_a |= ha; occupied_b |= hb
    return True

def partition_agreements(a,b):
    labels=validate_input(a,b)
    return {p for p in partitions(labels) if partition_valid(a,b,p)}

def compare_exact(expected,actual):
    if expected!=actual: raise AssertionError({'expected':repr(expected),'actual':repr(actual)})

def audit_rows(rows,expected):
    ids=[r['id'] for r in rows]
    if len(ids)!=len(set(ids)) or set(ids)!=set(expected): raise ValueError('missing/duplicate rows')

def budget_result(valid,budget):
    # Test adapter convention, not an assertion about the eventual candidate API.
    if type(budget) is not int or budget<0:raise ValueError('budget')
    optimum=min(map(len,valid))
    return ('optimal-forest',optimum) if optimum<=budget else ('bounded-negative',None)

def controls():
    frozen=json.loads((HERE/'FIXTURES-v1.json').read_text()); begun=time.perf_counter()
    rows=[]; observed={}; caught=[]
    for f in frozen['truth_cases']:
        validate_input(f['a'],f['b'])
        gp,graph_info=graph_agreements(f['a'],f['b']); pp=partition_agreements(f['a'],f['b'])
        compare_exact(set(gp),pp)
        optimum=min(map(len,pp)); optimal=sum(len(p)==optimum for p in pp)
        compare_exact((f['optimum'],f['valid_partition_count'],f['optimal_partition_count']),
                      (optimum,len(pp),optimal))
        row={'id':f['id'],'optimum':optimum,'valid':len(pp),'optimal':optimal,
             'partitions':[[list(b) for b in p] for p in sorted(pp)],'graph_bit_convention':graph_info}
        print(json.dumps(row,sort_keys=True)); rows.append(row);observed[f['id']]=pp
    for f in frozen['validity_cases']:
        p=canon_blocks(f['blocks']); gp,_=graph_agreements(f['a'],f['b'])
        compare_exact(f['valid'],partition_valid(f['a'],f['b'],p)); compare_exact(f['valid'],p in gp)
    for f in frozen['malformed_cases']:
        for route,check in [('partition-input',validate_input),('graph-input',graph_agreements)]:
            try:check(f['a'],f['b'])
            except ValueError:caught.append(route+'-'+f['id'])
            else:raise AssertionError('malformed accepted: '+f['id']+' '+route)
    original=observed['three_disagree']; removed=canon_blocks(((0,),(1,2)))
    incomplete=original-{removed}
    compare_exact(3,len(incomplete));compare_exact(2,min(map(len,incomplete)))
    try:compare_exact(original,incomplete)
    except AssertionError:caught.append('incomplete-cover-retains-optimum')
    else:raise AssertionError('incomplete cover escaped')
    try:compare_exact(2,1)
    except AssertionError:caught.append('wrong-optimum')
    else:raise AssertionError('comparator cannot fail')
    compare_exact(('bounded-negative',None),budget_result(observed['three_identical'],0))
    compare_exact(('bounded-negative',None),budget_result(original,1))
    compare_exact(('optimal-forest',2),budget_result(original,2))
    audit_rows(rows,[f['id'] for f in frozen['truth_cases']])
    for name,bad in [('missing-row',rows[:-1]),('duplicate-row',rows+[rows[0]])]:
        try:audit_rows(bad,[f['id'] for f in frozen['truth_cases']])
        except ValueError:caught.append(name)
        else:raise AssertionError(name+' escaped')
    print(json.dumps({'status':'CONTROL-PASS','truth_cases':len(rows),'validity_cases':len(frozen['validity_cases']),
                      'malformed_cases':len(frozen['malformed_cases']),'caught':caught,
                      'incomplete_cover_optimum_only_is_blind':True,'seconds':time.perf_counter()-begun},sort_keys=True))

def trees(labels):
    if len(labels)==1:return (labels[0],)
    ans=[]; first=labels[0]
    for mask in range(1<<(len(labels)-1)):
        left=(first,)+tuple(labels[i+1] for i in range(len(labels)-1) if mask>>i&1)
        right=tuple(x for x in labels if x not in left)
        if not right:continue
        for a in trees(left):
            for b in trees(right):ans.append((a,b))
    return tuple(ans)

def pilot(n):
    if n not in (3,4):raise ValueError('only frozen n3/n4 precontact pilots licensed here')
    begun=time.perf_counter(); tt=trees(tuple(range(n)))
    expected={3:3,4:15}[n];compare_exact(expected,len(tt))
    gs=[graph_forests(t)[0] for t in tt]; compared=0; histogram={}; windows=[]
    for i,a in enumerate(tt):
        start=time.perf_counter()
        for j,b in enumerate(tt):
            g={tuple(c[0] for c in key) for key in gs[i].keys() & gs[j].keys()}
            p=partition_agreements(a,b);compare_exact(g,p)
            opt=min(map(len,p));histogram[opt]=histogram.get(opt,0)+1;compared+=1
        windows.append(time.perf_counter()-start)
    compare_exact(expected**2,compared)
    print(json.dumps({'status':'FINITE-CROSS-METHOD-PASS','n':n,'tree_count':len(tt),'ordered_pairs':compared,
                      'partitions_per_pair':len(list(partitions(tuple(range(n))))),'optimum_histogram':histogram,
                      'row_seconds':windows,'seconds':time.perf_counter()-begun,
                      'universal_proof':False},sort_keys=True))

if __name__=='__main__':
    if sys.argv[1]=='controls':controls()
    elif sys.argv[1]=='pilot':pilot(int(sys.argv[2]))
    else:raise ValueError('mode')
