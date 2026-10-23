#!/usr/bin/env python3
"""Parent control replay using the initial arm's checker; not independent validation.
One-shot repair fixture driver. Existing toolkit has no rooted-MAF trace instrument.
"""
from pathlib import Path
import sys,json,time,hashlib
HERE=Path(__file__).resolve().parent
R=HERE.parents[1]
sys.path.insert(0,str(HERE.parent))
from reachable_trace import N,leaf,pair,rho,key,labels,maps,mark,cut,protected,eligible_pairs,classify,newick
from fractions import Fraction

# Parses only the frozen binary fixture syntax; rho supplied separately.
def parse(text):
    i=0
    def node():
        nonlocal i
        if text[i]=='(':
            i+=1;l=node();assert text[i]==',';i+=1;r=node();assert text[i]==')';i+=1
            return pair(l,r)
        j=i
        while i<len(text) and text[i] not in ',()':i+=1
        return leaf(text[j:i])
    out=node();assert i==len(text);return rho(out)
def oriented(f2,pair):
    ds=maps(f2)[2];return ds[pair[0]]>=ds[pair[1]]
def init(c):
    f1=parse(c['F1']);f2=parse(c['F2'])
    return mark(f1,c['protected_F1']),mark(f2,c['protected_F2'])
def advance_C(f1,f2,info):
    b=next(b for b in info['branches'] if b['name']=='C');assert b['legal']
    f1=mark(f1,b['protect1']);f2=mark(f2,b['protect2'])
    for target in b['cuts']:f1=cut(f1,target);f2=cut(f2,target)
    return f1,f2

def main():
    start=time.monotonic();raw=(HERE/'controls-frozen.json').read_bytes();spec=json.loads(raw);cs={x['id']:x for x in spec['controls']}
    out={'scope':'exact replay of frozen finite fixtures; no universal proof; same-author checker reuse disclosed','control_sha256':hashlib.sha256(raw).hexdigest(),'controls':[]}
    assert Fraction(1,4)+Fraction(1,8)+Fraction(3,16)==Fraction(9,16)>Fraction(1,2)
    out['controls'].append({'id':'nine-leaf-arithmetic','mass':'9/16','parent':'1/2','passed':True})
    # Tree traces independently recompiled in the separate retained Lean log.
    f1,f2=init(cs['live-two-leaf']);ab=cs['live-two-leaf']['chosen_pair'];assert oriented(f2,ab)
    ep,_=eligible_pairs(f1,f2);assert any(set(p)==set(ab) for p in ep)
    info=classify(f1,f2,ab);assert info['case']=='A3BC' and len(info['pendants'])==3 and all(b['legal'] for b in info['branches'])
    ff,gg=advance_C(f1,f2,info);child=classify(ff,gg,['a','x']);assert len(child['pendants'])==3
    live=[b['name'] for b in child['branches'] if b['legal']];assert live==['B']
    out['controls'].append({'id':'live-two-leaf','passed':True,'J':info,'C':child,'F1_C':newick(ff),'F2_C':newick(gg)})
    f1,f2=init(cs['wrong-orientation']);ab=cs['wrong-orientation']['chosen_pair'];assert not oriented(f2,ab)
    ff=cut(mark(f1,['x']),'y');gg=cut(mark(f2,['x']),'y');bad=classify(ff,gg,['a','x']);assert len(bad['pendants'])==1
    out['controls'].append({'id':'wrong-orientation','caught':True,'illegal_C_pendants':1})
    f1,f2=init(cs['orientation-positive-twin']);ab=cs['orientation-positive-twin']['chosen_pair'];assert oriented(f2,ab)
    info=classify(f1,f2,ab);assert info['case']=='A3BC' and all(b['legal'] for b in info['branches'])
    ff,gg=advance_C(f1,f2,info);child=classify(ff,gg,['a','y']);assert len(child['pendants'])==3
    out['controls'].append({'id':'orientation-positive-twin','passed':True,'C_pendants':3})
    out['elapsed_seconds']=time.monotonic()-start
    (R/'results/thesis-runtime-repair-controls.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'control_rows':len(out['controls']),'elapsed_seconds':out['elapsed_seconds']}))
if __name__=='__main__':main()
