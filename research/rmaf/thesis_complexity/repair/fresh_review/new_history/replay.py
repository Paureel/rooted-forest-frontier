"""Fresh-review lineage replay; parent history/geometry implementations unread.
Input is explicit candidate data. Credits are reconstructed from source phases.
"""
from fresh_checker_copy import *
BASE=Path(__file__).resolve().parent
DATA=ROOT/'results/thesis-runtime-repair-history-reachable-probe.json'
checks=[]
def eq(id,a,b):
    checks.append({'id':id,'passed':a==b,'observed':a,'expected':b})
    assert a==b,(id,a,b)
def shape(n):return n.name if not n.ch else (n.name,tuple(sorted((shape(x) for x in n.ch),key=repr)))
def forest_shape(f):return tuple(sorted((shape(t) for t in f),key=repr))
def negative(id,fn):
    try:fn()
    except AssertionError as e:checks.append({'id':id,'passed':True,'expected':'reject','observed':'reject','reason':str(e)});return
    raise AssertionError('corruption escaped: '+id)
def require_unprotected(st):
    assert not any(n.protected for idx in st.idx() for n in idx[0].values()),'initial state is not unprotected'
def snapshot(st):
    (i1,p1,d1,_),(i2,p2,d2,_)=st.idx()
    return {'protected1':sorted(k for k,n in i1.items() if n.protected),'protected2':sorted(k for k,n in i2.items() if n.protected),'eligible_best_pairs':[list(p) for p in choices(st)],'depth1':{k:d1[n] for k,n in i1.items() if not n.ch},'depth2':{k:d2[n] for k,n in i2.items() if not n.ch}}
def count(st,k):
    global count_nodes
    count_nodes+=1;assert count_nodes<=50000,'bounded continuation cap reached'
    if k<0:return 1,{'budget':k,'terminal':'negative','count':1}
    st=normalize(st)
    if st.active()<=2:return 1,{'budget':k,'terminal':'success','count':1}
    pair=choices(st)[0];inf=classify(st,pair);out={'budget':k,'rule':inf,'children':[]};total=1
    for br in inf['branches']:
        if br['legal']:
            child,tree=count(apply(st,br),k-len(br['cuts']));total+=child;out['children'].append({'branch':br['name'],'tree':tree})
    out['count']=total;return total,out
start=time.perf_counter();data=json.loads(DATA.read_text())
initial=State(parse(data['input_f1']),[parse(data['input_f2'])]);expected_labels=['B','W','X','Y','a','c','d','d0','h','t','x','y']
eq('F1-all-twelve-labels',sorted(initial.t.labels()),expected_labels)
eq('F2-all-twelve-labels',sorted(initial.f[0].labels()),expected_labels)
eq('labelled-unary-rho',[initial.t.name,len(initial.t.ch),initial.f[0].name,len(initial.f[0].ch)],['rho',1,'rho',1])
require_unprotected(initial)
corrupt=deepcopy(initial);index([corrupt.t])[0]['a'].protected=True
negative('corrupted-initial-protection',lambda:require_unprotected(corrupt))
st=deepcopy(initial);k=20;P=set();Q=set();replayed=[]
for ix,row in enumerate(data['rows']):
    snap=snapshot(st);(b1,p1,d1,_),(b2,p2,d2,_)=st.idx()
    eq(f'step{ix+1}-budget',k,row['budget'])
    eq(f'step{ix+1}-F1',repr(shape(st.t)),repr(shape(parse(row['f1']))))
    eq(f'step{ix+1}-F2',repr(forest_shape(st.f)),repr(forest_shape([parse(x) for x in row['f2']])))
    for key in ['protected1','protected2']:eq(f'step{ix+1}-{key}',snap[key],sorted(row[key]))
    inf=classify(st,row['rule']['pair'])
    for key in ['case','pendants','branches']:eq(f'step{ix+1}-{key}',inf[key],row['rule'][key])
    rec={'step':ix+1,'budget':k,'input_credits':{'P':sorted(P),'Q':sorted(Q)},'snapshot':snap,'rule':inf}
    if ix==2:
        # This new G1 already has physical a protection although its analysis P is empty.
        eq('new-I-empty-analysis-credit',[sorted(P),sorted(Q)],[[],[]])
        eq('new-I-inherited-physical-a',b1['a'].protected,True)
        eq('new-I-equal-F1-depth',d1[b1['a']],d1[b1['x']])
        eq('new-I-x-deeper-F2',d2[b2['x']]>d2[b2['a']],True)
        negative('new-I-ineligible-xy',lambda:classify(st,('x','y')))
        rec['depth_history_obstruction']={'a_F1_depth':d1[b1['a']],'x_F1_depth':d1[b1['x']],'a_F2_depth':d2[b2['a']],'x_F2_depth':d2[b2['x']],'xy_eligible':any(set(x)=={'x','y'} for x in choices(st))}
    if 'selected_branch' in row:
        br=next(br for br in inf['branches'] if br['name']==row['selected_branch']);assert br['legal']
        legal=[br['name'] for br in inf['branches'] if br['legal']]
        # Explicit source phase interpretation, checked against physical prerequisites.
        if ix==0:
            assert P==Q==set() and inf['case']=='A2BC' and br['name']=='C'
            P={'a'};Q=set();rule='p118 G1 A2 C assignment'
        elif ix==1:
            assert P=={'a'} and inf['case']=='A3BC' and legal==['A']
            assert set(inf['pair'])=={'a','d0'}
            P=set();Q=set();rule='p120 G3 sole surviving A3 branch resets analysis credits'
        elif ix==2:
            assert P==Q==set() and inf['case']=='A2BC' and legal==['C']
            P={'a'};Q=set();rule='p118 new G1 A2 C assignment; all-three-legal is not a premise'
        elif ix==3:
            assert P=={'a'} and Q==set() and inf['case']=='A2BC' and legal==['B','A'] and br['cuts']==['d']
            P={'a'};Q=set();rule='p120 G3 old A2/current A2 endpoint continuation retains a and Q empty'
        rec['credit_source_rule']=rule;rec['selected_branch']=br['name'];rec['output_credits']={'P':sorted(P),'Q':sorted(Q)}
        eq(f'step{ix+1}-output-credits',rec['output_credits'],row['output_credits'])
        k-=len(br['cuts']);st=apply(st,br)
    replayed.append(rec)
# Final target's physical and analysis predicates.
(b1,p1,d1,_),(b2,p2,d2,_)=st.idx();a=b2['a'];b=sibling(a,p2)
eq('J-input-credits',[sorted(P),sorted(Q)],[['a'],[]]);eq('J-case',inf['case'],'A3BC');eq('J-three-pendants',len(inf['pendants']),3)
eq('J-all-three-legal',[br['name'] for br in inf['branches'] if br['legal']],['A','B','C'])
eq('J-three-e-active-roots',len(p1[p1[b1['x']]].labels()),3)
eq('J-a-and-b-physical-protection',[a.protected,b.protected],[True,True]);eq('J-x-inside-b','x' in b.labels(),True)
fire={'failing_step':'unqualified source-history implication to x outside protected sibling b','scope':'source-reachable physical full-call-tree history with source-derived G1/G3 credit schedule; not a conditional local theorem or runtime-bound counterexample','instance':{'input_f1':data['input_f1'],'input_f2':data['input_f2'],'root':'labelled unary rho','initial_budget':20,'branch_sequence':['C','A','C','A'],'J_budget':k,'J_pair':['x','y'],'P':sorted(P),'Q':sorted(Q),'b':b.key(),'e_active_roots':['x','y','h']},'lhs':1,'rhs':0,'residual':1,'quantity':'indicator that x belongs to b; claimed outside-b conclusion requires zero'}
count_nodes=0;C=apply(st,next(br for br in inf['branches'] if br['name']=='C'));calls,tree=count(C,k-1)
record={'status':'checked reachable application fire','input_sha256':hashlib.sha256(DATA.read_bytes()).hexdigest(),'checks':checks,'replayed':replayed,'fire':fire,'actual_C':{'count':calls,'budget':k-1,'scope':'full legal children under deterministic allowed tie selection; invocation counted','tree':tree},'elapsed_seconds':time.perf_counter()-start,'lineage':'own first-review tree evaluator; no parent history implementation read or imported; explicit input and expected snapshots exposed'}
(ROOT/'results/thesis-runtime-repair-fresh-review-history-replay.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'fire':fire,'actual_C_count':calls,'elapsed_seconds':record['elapsed_seconds']}))
