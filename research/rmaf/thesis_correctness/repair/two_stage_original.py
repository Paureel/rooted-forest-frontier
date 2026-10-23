"""Direct current-edge witness; does not use suppressed edge identity for either exchange."""
import hashlib,json,pathlib,sys
BASE=pathlib.Path('/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf');HERE=BASE/'thesis_correctness/repair'
sys.path.insert(0,str(HERE.parent))
from local_obligations import controls,component_data,info,all_optimal_cuts
from algorithm import Forest

def af(f1,f2,cuts):
    used=set()
    for b in component_data(f2,cuts):
        s1,v1=info(f1,b);s2,_=info(f2,b)
        if s1 is None or s1!=s2 or used&v1:return False
        used|=v1
    return True

def normalize(f2,cuts,path,u):
    out=cuts-set(path);p={v:w for w,cs in f2.child.items() for v in cs}
    if len(cuts&set(path))>=2 and u in p:out.add(u)
    return out

def main():
    controls();p=HERE/'two-stage-original-spec.json';s=json.loads(p.read_text())
    f1,f2=Forest.tree(s['t1']),Forest.tree(s['t2']);parent={v:w for w,cs in f2.child.items() for v in cs}
    leaves={next(iter(l)):v for v,l in f2.label.items()};a,c,x=(leaves[z] for z in ['a','c','x'])
    def up(v):
        ans=[v]
        while v in parent:v=parent[v];ans.append(v)
        return ans
    aa,cc=up(a),up(c);u=next(v for v in aa if v in cc)
    path=set(aa[:aa.index(u)]+cc[:cc.index(u)]);v=parent[u]
    assert parent[x]==v
    B={leaves[z] for z in ['b1','b2']}
    d,opts=all_optimal_cuts(f1,f2);assert d==s['expected_optimum']
    rows=[]
    for names in s['positive_cutsets']:
        E={leaves[z] for z in names};assert frozenset(E) in opts
        E1=normalize(f2,E|B,path,u);E2=normalize(f2,E1,{x,u},v)
        assert af(f1,f2,E1) and af(f1,f2,E2) and E2==B
        rows.append({'input':names,'E':sorted(E),'E1':sorted(E1),'E2':sorted(E2),'counts':[len(E),len(E1),len(E2)],'first_AF':True,'second_AF':True})
    corruptions=[not af(f1,f2,B-{b}) for b in B];assert all(corruptions)
    out={'status':'two-controlled-original-edge-traces-pass','optimum':d,'optimal_cutsets':len(opts),'a_c_path':sorted(path),'second_path_original_IDs':sorted({x,u}),'common_parent_original_ID':v,'pendant_original_IDs':sorted(B),'traces':rows,'corruptions_caught':len(corruptions),'scope':s['scope'],'open':'A general AF-preserving transport/composition theorem is still required.','provenance':'Earlier same-author raw-cut AF checker reused; algorithm provides only tree construction, not AF decisions or cut/reduce calls.','spec_sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
    target=BASE/'results/thesis-correctness-repair-two-stage-original.json';target.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'controls':2,'corruptions_caught':2,'traces':rows,'receipt':str(target)}))
if __name__=='__main__':main()
