#!/usr/bin/env python3
"""Postrelease controls of the actual data comparator, preserving every copy."""
import copy,json,subprocess,sys
from pathlib import Path
P=Path(__file__).resolve().parent; data=json.loads((P/'readouts-run3.log').read_text())
folder=P/'readout-mutants'; folder.mkdir(exist_ok=True)
plants=[]
for name in ['paid','cut','source-drop','unpaid','priority','agreement']:
    d=copy.deepcopy(data)
    if name=='paid': d['cases'][3]['pendantChild']['paid']=0
    if name=='cut': d['cases'][3]['cuts'][0]='1111111'
    if name=='source-drop': d['cases'][3]['pendantChild']['sourceForest'].pop()
    if name=='unpaid': d['cases'][3]['remaining'][0]=0
    if name=='priority': d['priority'][0]['selected']['category']='t1'
    if name=='agreement': d['cases'][1]['Fagreement']=False
    file=folder/(name+'.json'); file.write_text(json.dumps(d,indent=2)+'\n')
    r=subprocess.run([sys.executable,str(P/'compare_readouts_v2.py'),str(file)],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (folder/(name+'.log')).write_text(r.stdout)
    assert r.returncode!=0,('actual comparator mutation survived',name)
    plants.append({'mutation':name,'caught':True,'returncode':r.returncode})
r=subprocess.run([sys.executable,str(P/'compare_readouts_v2.py')],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(folder/'clean.log').write_text(r.stdout); assert r.returncode==0
(P/'readout-mutation-receipt-v1.json').write_text(json.dumps({'scope':'postcontact comparator plants','mutations':plants,'clean_twin':True},indent=2)+'\n')
print(json.dumps({'mutations_caught':len(plants),'required':6,'clean_twin':True}))
