#!/usr/bin/env python3
"""One-shot exact-source panel from the already frozen independent LCA oracle.
The same all-shapes/all-labellings family is used for the pilot and full panel.
Kernel decide checks both the unchanged extractor and selected-occurrence lists.
"""
import argparse,itertools,json,os,subprocess,time
from pathlib import Path
from independent_lca_check import shapes,fill,terminals,lca_hull
from rebuild import HERE,ROOT,BUILD,digest

def tree(t):
    if isinstance(t,str): return '(.leaf '+str(ord(t)-ord('a'))+')'
    return '(.node '+tree(t[0])+' '+tree(t[1])+')'
def addresses(vs):
    return '['+','.join('['+','.join('false' if bit=='0' else 'true' for bit in v)+']' for v in sorted(vs))+']'
def run(bound):
    code=['import RMAF','import TreeAddresses','open RMAF LeastEmbedding','namespace FreshSourcePanel']
    count=0
    for n in range(1,bound+1):
        for shape in shapes(n):
            for labels in itertools.product('ab',repeat=n):
                t=fill(shape,iter(labels))
                for selected in ([],['a'],['b'],['a','b'],['a','a'],['a','b','a'],['z']):
                    u=terminals(t,selected); h=lca_hull(u)
                    ls='['+','.join(str(ord(c)-ord('a')) for c in selected)+']'
                    name=f'case{count:04d}'
                    code.append(f'theorem {name} : minimalVertices {ls} {tree(t)} = {addresses(h)} ∧ terminals {ls} {tree(t)} = {addresses(u)} := by decide')
                    code.append(f'#print axioms {name}')
                    count+=1
    code.append('end FreshSourcePanel')
    p=BUILD/f'FiniteSourcePanel{bound}.lean';p.write_text('\n'.join(code)+'\n')
    env=os.environ.copy();env['LEAN_PATH']=str(BUILD)
    before=time.monotonic()
    proc=subprocess.run([str(ROOT/'bootloops-lean'),str(p)],cwd=BUILD,env=env,capture_output=True,text=True,timeout=60)
    output=proc.stdout+proc.stderr
    log=HERE/f'source-panel-{bound}.log';log.write_text(output)
    zero_count=output.count('does not depend on any axioms')
    receipt=dict(bound=bound,cases=count,equalities=2*count,returncode=proc.returncode,seconds=time.monotonic()-before,
                 zero_axiom_reports=zero_count,source_sha256=digest(p),log_sha256=digest(log))
    (HERE/f'source-panel-{bound}.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt))
    assert proc.returncode==0 and ': error:' not in output and zero_count==count,output[:2000]
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--max-leaves',type=int,required=True);a=p.parse_args();run(a.max_leaves)
