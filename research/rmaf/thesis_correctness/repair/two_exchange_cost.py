"""Small exact control/census for the separately Lean-checked scalar bound."""
import hashlib,itertools,json,pathlib,time
ROOT=pathlib.Path('/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf')
HERE=ROOT/'thesis_correctness/repair'
def final(t):
    base,p1,p2,p3,added,r1,n2,r2=t
    return max(max(base+added-p3,0)+r1-n2,0)+r2
def premises(t):
    base,p1,p2,p3,added,r1,n2,r2=t
    return [p2<=2,p3>=1,p1+p2+p3>=2,added+p2<=2,r1<=1,p3!=1 or r1==0,p3!=1 or p1<=n2,p3<2 or n2>=1,r2<=1,n2>1 or r2==0,p3<=base+added,n2<=max(base+added-p3,0)+r1]
def main():
    start=time.perf_counter();spec=json.loads((HERE/'two-exchange-cost-spec.json').read_text());checks=[]
    for case in spec['positive_controls']:
        t=case['tuple'];actual=final(t)
        assert all(premises(t)) and actual==case['expected_final'] and actual<=t[0]
        checks.append({'name':case['name'],'passed':True,'actual':actual})
    for case in spec['negative_controls']:
        t=case['tuple'];actual=final(t)
        assert not all(premises(t)) and actual==case['expected_final'] and actual>t[0]
        checks.append({'name':case['name'],'caught':True,'actual':actual,'failed_premises':[i for i,v in enumerate(premises(t)) if not v]})
    controls_seconds=time.perf_counter()-start
    checked=0
    for t in itertools.product(range(7),range(3),range(3),range(1,5),range(3),range(2),range(7),range(2)):
        if all(premises(t)):
            checked+=1
            assert final(t)<=t[0],t
    log=(ROOT/'results/thesis-correctness-repair-two-exchange-lean.log').read_text()
    assert "depends on axioms: [propext, Quot.sound]" in log
    receipt={'status':'checked-local-scalar','controls':checks,'finite_valid_tuples':checked,'finite_failures':0,'control_seconds':controls_seconds,'total_seconds':time.perf_counter()-start,'lean_log':log.strip(),'protocol_limitation':'Spec frozen before construction, but controls executed after initial Lean compile. These are author checks; independent review remains required.','scope':spec['scope'],'files':[{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in [HERE/'two-exchange-cost-spec.json',HERE/'TwoExchangeCost.lean',pathlib.Path(__file__)]]}
    out=ROOT/'results/thesis-correctness-repair-two-exchange.json';out.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'controls':len(checks),'valid_tuples':checked,'failures':0,'seconds':receipt['total_seconds'],'receipt':str(out)}))
if __name__=='__main__':main()
