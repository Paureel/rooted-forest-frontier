"""Audit executed isolated Lean logs, retaining complete theorem dependencies."""
import hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent; D=HERE/'lean-isolated'; OUT=HERE.parents[1]/'results'
def strip_comments(s):
    out=[]; i=0; depth=0
    while i<len(s):
        if s[i:i+2]=='/-': depth+=1; i+=2
        elif depth and s[i:i+2]=='-/': depth-=1; i+=2
        elif depth: i+=1
        elif s[i:i+2]=='--':
            j=s.find('\n',i); i=len(s) if j<0 else j
        else: out.append(s[i]); i+=1
    assert depth==0
    return ''.join(out)
accepted={ 'RMAF':21,'FailedFrontier':10,'Audit':10,'MassChecks':4,'ConditionalCover':6,'Retarget233':4 }
rows=[]
for mod,count in accepted.items():
    p=D/(mod+'.lean'); src=p.read_text(); clean=strip_comments(src)
    forbidden=re.findall(r'\b(?:sorry|admit|axiom|native_decide)\b',clean)
    assert not forbidden,(mod,forbidden)
    assert (D/(mod+'.olean')).exists()
    log=(D/(mod+'.log')).read_text()
    expected=re.findall(r'^#print axioms\s+(.+)$',src,re.M)
    found=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log,re.S)
    assert len(expected)==count and len(found)==count,(mod,len(expected),len(found))
    axioms=[]
    for name,dep in found:
        deps=[x.strip() for x in dep.split(',') if x.strip()]
        assert set(deps)<= {'propext','Classical.choice','Quot.sound'},(name,deps)
        axioms.append({'name':name,'axioms':deps})
    rows.append({'module':mod,'statements':count,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'log_sha256':hashlib.sha256((D/(mod+'.log')).read_bytes()).hexdigest(),'forbidden_constructs':forbidden,'axiom_inventory':axioms,'scope':'kernel proposition only; model-to-original-graph interface not supplied'})
neg=[]
for mod in ['FalseFrontier','FalseMassPlant','Retarget233Negative']:
    log=(D/(mod+'.log')).read_text()
    assert 'proved that the proposition' in log and 'is false' in log
    neg.append({'module':mod,'rejected_for_false_proposition':True,'log':log})
receipt={'isolated_directory':str(D),'dependency_RMAF_rebuilt':True,'candidate_accepted_distinct_statements':24,'dependency_statements':21,'audit_duplicate_prints':10,'rows':rows,'negative_controls':neg,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'no_custom_axiom_or_placeholder':True,'scope':'B ten executable-model+four arithmetic; A six conditional/arithmetic; retarget four arithmetic. Original graph correspondence remains OPEN.'}
(OUT/'algorithm-review-lean-replay-and-axioms.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'B':14,'A':6,'retarget':4,'dependency':21,'false_propositions_rejected':3}))
