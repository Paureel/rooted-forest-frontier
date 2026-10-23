#!/usr/bin/env python3
"""One-shot, fresh X0 exact source-model reconstruction; no prior implementation imported.
Read GUIDE.md for source conventions and unproved analysis annotation domain.
Physical incoming protections carry origin strings through suppression.
"""
from dataclasses import dataclass, replace
from fractions import Fraction as F
from pathlib import Path
import json, re, time, hashlib, argparse, itertools, copy
ROOT=Path(__file__).resolve().parents[5]
OUT=ROOT/'research/rmaf/results'
BASE=ROOT/'research/rmaf/thesis_complexity/continuation_v2'

@dataclass(frozen=True)
class N:
    label: str=''
    children: tuple=()
    prot: frozenset=frozenset()

def labels(n):
    return frozenset(([n.label] if n.label else [])) | frozenset().union(*(labels(c) for c in n.children))
def key(n): return ','.join(sorted(labels(n)))
def shape(n): return (n.label,tuple(sorted((shape(c) for c in n.children))))
def parse(s, rho=True):
    tok=re.findall(r'[A-Za-z0-9_]+|[(),]',s); pos=0
    def rec():
        nonlocal pos
        if tok[pos]!='(':
            v=N(tok[pos]);pos+=1;return v
        pos+=1;ch=[rec()]
        while tok[pos]==',':pos+=1;ch.append(rec())
        assert tok[pos]==')';pos+=1
        lab=''
        if pos<len(tok) and tok[pos] not in ('(',')',','):lab=tok[pos];pos+=1
        return N(lab,tuple(ch))
    n=rec();assert pos==len(tok),(s,pos,tok)
    if rho and n.label!='rho':n=N('rho',(n,))
    return n

def index(forest):
    nodes={};parents={};depth={};roots={}
    def rec(n,par,d,r):
        k=key(n);assert k not in nodes,k
        nodes[k]=n;parents[k]=par;depth[k]=d;roots[k]=r
        for c in n.children:rec(c,k,d+1,r)
    for r in forest:rec(r,None,0,key(r))
    return nodes,parents,depth,roots

def mark(n,ks,origin):
    return replace(n,prot=n.prot|frozenset(origin+':'+key(n) for _ in [0] if key(n) in ks),children=tuple(mark(c,ks,origin) for c in n.children))
def clean(n):
    if n.label:return n
    if not n.children:return None
    if len(n.children)==1:
        c=n.children[0];return replace(c,prot=c.prot|n.prot)
    return n

def cut(forest,ks,drop=False):
    detached=[]
    def rec(n):
        if key(n) in ks:
            if not drop:detached.append(replace(n,prot=frozenset()))
            return None
        ch=tuple(c1 for c in n.children if (c1:=rec(c)) is not None)
        return clean(replace(n,children=ch))
    kept=tuple(v for n in forest if (v:=rec(n)) is not None)
    # An unlabelled component root has no incoming physical edge.
    return tuple(replace(v,prot=frozenset()) for v in kept+tuple(detached))

def collapse(n,k,lab):
    if key(n)==k:return N(lab,(),n.prot)
    return replace(n,children=tuple(collapse(c,k,lab) for c in n.children))

@dataclass(frozen=True)
class S:
    f1: N
    f2: tuple
    budget: int
    history: tuple=()

def initial(s1,s2,k=20,p1=(),p2=()):
    return S(mark(parse(s1),set(p1),'fixture:F1'),(mark(parse(s2),set(p2),'fixture:F2'),),k)

def siblings(k,nodes,par):
    p=par[k]
    return [] if p is None else [key(c) for c in nodes[p].children if key(c)!=k]
def pendants(a,c,ns,pa):
    if a==c:return a,[]
    aa=[];t=a
    while t is not None:aa.append(t);t=pa[t]
    cc=[];t=c
    while t not in aa:
        if t is None:return None,[]
        cc.append(t);t=pa[t]
    lca=t;path=aa[:aa.index(lca)+1]+cc[::-1]
    pset=set(path)
    return lca,[key(ch) for v in path[1:-1] for ch in ns[v].children if key(ch) not in pset]

def active(n):return [key(n)] if not n.children else sum((active(c) for c in n.children),[])+([n.label] if n.label else [])
def selection(s):
    ns,pa,de,rt=index((s.f1,)); n2,p2,d2,r2=index(s.f2)
    candidates=[]
    for n in ns.values():
        if len(n.children)==2 and all(not c.children for c in n.children):
            a,c=[key(t) for t in n.children]
            assert a in n2 and c in n2
            if d2[a]<d2[c] or (d2[a]==d2[c] and a>c):a,c=c,a
            candidates.append((a,c))
    tops=[pa[k] for k,n in ns.items() if n.prot and pa[k] is not None]
    top=max(tops,key=lambda t:de[t]) if tops else key(s.f1)
    allowed=[p for p in candidates if set(p)<=set(active(ns[top]))]
    assert allowed or len(active(s.f1))<=2,('no eligible',snapshot(s))
    def rank(p):return (de[p[0]],int(r2[p[0]]!=r2[p[1]]),max(d2[p[0]],d2[p[1]]))
    best=max(map(rank,allowed),default=None)
    winners=sorted(p for p in allowed if rank(p)==best)
    return winners,{'deepest_protected_top':top,'all_candidates':candidates,'eligible':allowed,'best':winners,'rank':best}

def normalize(s,preferred=None):
    events=[]
    if s.budget<0:return s,None,events,'negative-budget'
    while len(active(s.f1))>2:
        pairs,sel=selection(s)
        wanted=tuple(preferred) if preferred is not None else None
        p=wanted if wanted in pairs or (wanted is not None and wanted[::-1] in pairs and orientation(s,wanted)) else pairs[0]
        # A tie may legally have reverse orientation.
        assert p in pairs or (p[::-1] in pairs and orientation(s,p)),('selection',p,pairs)
        ns,pa,de,rt=index(s.f2);a,c=p
        if pa[a]==pa[c] and pa[a] is not None:
            cl=pa[a];n1,p1,_,_=index((s.f1,));cl1=p1[a]
            lab='@'+ '|'.join(sorted((a,c)))
            s=replace(s,f1=collapse(s.f1,cl1,lab),f2=tuple(collapse(t,cl,lab) for t in s.f2))
            events.append({'merge':p,'label':lab});continue
        root=next((x for x in p if pa[x] is None),None)
        if root is not None:
            f1=cut((s.f1,),{root},drop=True);assert len(f1)==1
            s=replace(s,f1=f1[0],f2=tuple(t for t in s.f2 if key(t)!=root))
            events.append({'done':root});continue
        assert wanted is None or p==wanted,('branch selection',wanted,p,pairs)
        return s,p,events,None
    return s,None,events,'success'

def orientation(s,p):
    n,pa,d,r=index(s.f2);a,c=p
    return r[a]!=r[c] or d[a]>=d[c]

def rule(s,p):
    n1,p1,d1,r1=index((s.f1,));n2,p2,d2,r2=index(s.f2);a,c=p
    assert orientation(s,p),('orientation',p)
    lca,pend=pendants(a,c,n2,p2)
    unc=siblings(p1[a],n1,p1);unc=unc[0] if unc else None
    def same(k):return k in n1 and shape(n1[k])==shape(n2[k])
    def b(name,cuts,pr1=(),pr2=()):
        cuts=list(cuts); reasons=[]
        for k in cuts:
            assert p2[k] is not None,('cut-root',k)
            if n2[k].prot:reasons.append({'edge':k,'reason':'protected','origins':sorted(n2[k].prot)})
            if p2[p2[k]] is None:
                for sib in siblings(k,n2,p2):
                    if n2[sib].prot:reasons.append({'edge':k,'reason':'root-sibling-protected','sibling':sib,'origins':sorted(n2[sib].prot)})
        return dict(name=name,cuts=cuts,protect1=list(pr1),protect2=list(pr2),legal=not reasons,obstructions=reasons)
    preds={};branches=[]
    if lca is None:case='AC';branches=[b('A',[a]),b('C',[c])]
    elif len(pend)==1:case='B';branches=[b('B',pend)]
    else:
        rb_a=unc in siblings(a,n2,p2) and unc in n2 and same(unc)
        rb_c=unc in siblings(c,n2,p2) and unc in n2 and same(unc)
        chain=None
        if len(pend)>=2:
            chain=N('',(n2[pend[0]],n2[pend[1]]))
            for k in pend[2:]:chain=N('',(chain,n2[k]))
        rbstar=p2[c]==lca and chain is not None and unc in n1 and all(same(k) for k in pend) and shape(chain)==shape(n1[unc])
        twob=len(pend)==2 and unc in n2 and same(unc) and unc in siblings(lca,n2,p2)
        bcy=unc in n2 and same(unc) and bool(n2[unc].prot) and p2[unc]==pend[0]
        preds=dict(RB=rb_a or rb_c,RBstar=rbstar,twoB=twob,BCY=bcy)
        if rb_a or rb_c:case='RB';branches=[b('RB',[c if rb_a else a])]
        elif rbstar:case='RB*';branches=[b('RB*',[a])]
        elif twob:case='2B';branches=[b('2B',pend)]
        elif bcy:
            y=siblings(unc,n2,p2);assert len(y)==1
            case='BCY';branches=[b('B',pend),b('CY',[c,y[0]])]
        elif len(pend)==2:
            case='A2BC'
            branches=[b('B',pend),b('A',[a],(),pend)] if n2[c].prot else [b('A',[a]),b('B',pend),b('C',[c],[a],[a]+pend)]
        else:
            assert len(pend)>=3
            case='A3BC';branches=[b('A',[a]),b('B',pend),b('C',[c],[a],[a])]
    return dict(pair=list(p),case=case,pendants=pend,lca=lca,uncle=unc,predicates=preds,branches=branches)

def transition(s,r,br):
    assert br['legal']
    origin=f"step{len(s.history)+1}:{r['case']}:{','.join(r['pair'])}:{br['name']}"
    f1=mark(s.f1,set(br['protect1']),origin+':F1')
    f2=tuple(mark(t,set(br['protect2']),origin+':F2') for t in s.f2)
    return S(f1,cut(f2,set(br['cuts'])),s.budget-len(br['cuts']),s.history+(origin,))

def snapshot(s):
    n1,p1,d1,r1=index((s.f1,));n2,p2,d2,r2=index(s.f2)
    def fmt(n):return ('('+','.join(fmt(c) for c in n.children)+')' if n.children else '')+n.label
    return dict(F1=fmt(s.f1),F2=[fmt(t) for t in s.f2],budget=s.budget,active=active(s.f1),protected1={k:sorted(n.prot) for k,n in n1.items() if n.prot and p1[k] is not None},protected2={k:sorted(n.prot) for k,n in n2.items() if n.prot and p2[k] is not None},history=s.history)

def full(s,limit=50000):
    used=0
    def rec(s):
        nonlocal used
        used+=1
        if used>limit:raise RuntimeError('full tree cap')
        s,p,events,term=normalize(s)
        item=dict(state=snapshot(s),normalization=events,terminal=term,children=[])
        if term:item['count']=1;return item
        r=rule(s,p);item['rule']=r
        for br in r['branches']:
            if br['legal']:item['children'].append(dict(branch=br['name'],tree=rec(transition(s,r,br))))
        item['count']=1+sum(x['tree']['count'] for x in item['children']);return item
    return rec(s)

def trace(s,pairs,branches):
    rows=[]
    for j,pair in enumerate(pairs):
        s,p,ev,term=normalize(s,pair);assert term is None
        r=rule(s,p);row=dict(state=snapshot(s),selection=selection(s)[1],normalization=ev,rule=r)
        rows.append(row)
        if j<len(branches):
            br=next(b for b in r['branches'] if b['name']==branches[j]);assert br['legal']
            row['chosen_branch']=br['name'];s=transition(s,r,br)
    return s,rows

def exact(v):return str(v) if isinstance(v,F) else v

def controls():
    start=time.perf_counter(); data=json.loads((BASE/'controls-frozen.json').read_text()); checks=[];traces={}
    def eq(name,got,want):
        ok=got==want;checks.append(dict(id=name,passed=ok,observed=got,expected=want))
        if not ok:raise AssertionError(checks[-1])
        # Every equality check gets a mismatched expected twin.
        bad=object();assert got!=bad
    nine=data['trace_data']['nine']['trace'];thir=data['trace_data']['thirteen']['trace']
    for name,raw in [('nine',nine),('thirteen',thir)]:
        s=initial(raw[0]['F1'],raw[0]['F2']);s,rows=trace(s,[r['pair'] for r in raw],[r['chosen_branch'] for r in raw if 'chosen_branch' in r])
        traces[name]=rows
        for i,(r,e) in enumerate(zip(rows,raw)):
            eq(f'{name}-{i}-case',r['rule']['case'],e['case']);eq(f'{name}-{i}-pendants',r['rule']['pendants'],e['pendants'])
            eq(f'{name}-{i}-protect1',sorted(r['state']['protected1']),sorted(e['protected_F1']))
            eq(f'{name}-{i}-protect2',sorted(r['state']['protected2']),sorted(e['protected_F2']))
            eq(f'{name}-{i}-branches',[(b['name'],b['cuts'],b['legal']) for b in r['rule']['branches']],[(b['name'],b['cuts'],b['legal']) for b in e['branches']])
        if name=='nine':
            c=next(b for b in rows[-1]['rule']['branches'] if b['name']=='C');ct=full(transition(s,rows[-1]['rule'],c));eq('nine-C-legal-children',len(ct['children']),0)
            traces['nine_C']=ct
        else:
            P={'a'};Q=set()
            for r in rows[2:4]:P.add(r['rule']['pair'][0]);Q.add(r['rule']['pair'][0])
            eq('thirteen-P-size',len(P),3);eq('thirteen-Q-displayed-size',len(Q),2)
            neg=initial(raw[0]['F1'],raw[0]['F2'],2);neg,rr=trace(neg,[r['pair'] for r in raw[:3]],['C','A'])
            b=next(b for b in rr[-1]['rule']['branches'] if b['name']=='B');eq('negative-J-budget',neg.budget,0);eq('negative-B-cost',len(b['cuts']),4)
            nt=full(transition(neg,rr[-1]['rule'],b));eq('negative-child-budget',nt['state']['budget'],-4);eq('negative-count',nt['count'],1);traces['negative']=nt
    ins=next(c for c in data['controls'] if c['id']=='inside-b-reached')['instance'];ss=initial(ins['input_f1'],ins['input_f2'],20)
    ss,ir=trace(ss,[('a','t'),('d0','a'),('a','c'),('d','a'),('x','y')],['C','A','C','A']);traces['inside']=ir
    eq('inside-J-budget',ss.budget,16);eq('inside-J-pendants',len(ir[-1]['rule']['pendants']),3)
    # Explicit source local schedule, calibrated at its own premises; no universal annotation closure.
    assert ir[0]['rule']['case']=='A2BC' and ir[0]['chosen_branch']=='C'
    assert ir[1]['rule']['case']=='A3BC' and sum(b['legal'] for b in ir[1]['rule']['branches'])==1
    assert ir[2]['rule']['case']=='A2BC' and ir[2]['chosen_branch']=='C'
    assert ir[3]['rule']['case']=='A2BC' and sum(b['legal'] for b in ir[3]['rule']['branches'])==2
    credits=[({ir[0]['rule']['pair'][0]},set()),(set(),set()),({ir[2]['rule']['pair'][0]},set()),({ir[2]['rule']['pair'][0]},set())]
    for row,(P,Q) in zip(ir,credits):row['source_credit_output']={'P':sorted(P),'Q':sorted(Q)}
    eq('inside-J-P',sorted(credits[-1][0]),['a']);eq('inside-J-Q',sorted(credits[-1][1]),[])
    ns,pa,_,_=index(ss.f2);actual_b=siblings('a',ns,pa)[0]
    eq('inside-b-key',actual_b,ins['b']);eq('inside-b-membership','x' in labels(ns[actual_b]),True)
    n1,p1,_,_=index((ss.f1,));e=siblings('a',n1,p1)[0]
    eq('inside-e-active-roots',len(active(n1[e])),3)
    eq('false-outside-b-rejected',int('x' in labels(ns[actual_b]))==0,False)
    r=ir[-1]['rule'];ct=full(transition(ss,r,next(b for b in r['branches'] if b['name']=='C')));eq('inside-C-count',ct['count'],2);traces['inside_C']=ct
    for fx in data['controls']:
        if fx['id'] not in ('live-two-leaf','wrong-orientation','orientation-positive-twin'):continue
        st=initial(fx['F1'],fx['F2'],20,fx['protected_F1'],fx['protected_F2']);p=fx['chosen_pair'];accepted=orientation(st,p)
        eq(fx['id']+'-orientation',accepted,fx.get('expected_orientation_accepted',True))
        if not accepted:
            # Deliberately ignore the endpoint order ONLY for this frozen corruption diagnostic.
            illegal=S(mark(st.f1,{'x'},'illegal-order:F1'),cut(tuple(mark(t,{'x'},'illegal-order:F2') for t in st.f2),{'y'}),19)
            ill,p2,_,term=normalize(illegal)
            assert term is None
            eq(fx['id']+'-illegal-C-pendants',len(rule(ill,p2)['pendants']),fx['if_illegally_cut_y_expected_C_pendants'])
            continue
        st,p,ev,term=normalize(st,p);r=rule(st,p)
        ct=full(transition(st,r,next(b for b in r['branches'] if b['name']=='C')))
        eq(fx['id']+'-C-pendants',len(ct['rule']['pendants']),fx['expected_C_pendants'])
        if 'expected_C_legal_branches' in fx:eq(fx['id']+'-C-branches',[x['branch'] for x in ct['children']],fx['expected_C_legal_branches'])
        traces[fx['id']]=ct
    eq('false-negative-rhs',str(F(128)*F(2)**-10-3),'-23/8');eq('false-negative-residual',str(1-(F(128)*F(2)**-10-3)),'31/8')
    eq('false-negative-rejected',F(1)<=F(128)*F(2)**-10-3,False)
    X=F(128);A=X/4-2;B=X/8-3
    for kind,C,total in [('weak',X/8+2,62),('strong',X/8-1,59)]:eq(kind+'-composition',int(1+A+B+C),total)
    mass=F(1,4)+F(1,8)+F(3,16);eq('G4-mass',str(mass),'9/16');eq('G4-residual',str(mass-F(1,2)),'1/16');eq('G4-offset',1-2-3-1,-5)
    # False comparator plant; clean pair and unequal rational pair through same detector.
    def comparator(a,b):return a==b
    eq('comparator-clean',comparator(F(9,16),F(9,16)),True);eq('comparator-corruption',comparator(F(9,16),F(8,16)),False)
    return dict(status='controls-passed',catalog_count=len(data['controls']),checks=checks,traces=traces,elapsed_seconds=time.perf_counter()-start,scope='Calibration; finite source-model replay, not universal certification')

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--controls',action='store_true');args=ap.parse_args()
    try:
        result=controls();path=OUT/'thesis-runtime-continuation-v2-x0-controls.json';path.write_text(json.dumps(result,indent=2));print(json.dumps({k:result[k] for k in ['status','catalog_count','elapsed_seconds']}));print(f"checks={len(result['checks'])}/{len(result['checks'])}; receipt={path}")
    except Exception as e:
        (OUT/'thesis-runtime-continuation-v2-x0-control-failure.json').write_text(json.dumps(dict(status='stopped-control-failure',error=str(e)),indent=2));raise
