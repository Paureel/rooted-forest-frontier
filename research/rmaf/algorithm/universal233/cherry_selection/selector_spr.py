"""One-shot exact adversary extending the existing cherry-selector wrappers.
No new general toolkit capability; imports are author DEVELOPMENT contacts.
"""
from pathlib import Path
import argparse,json,time,hashlib
from family import *

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--moving',type=int,nargs='+',required=True);p.add_argument('--out',required=True);a=p.parse_args();start=time.perf_counter();ctls=controls()
 base=json.loads((ROOT/'results/algorithm-universal233-pair-clusterfree-v1.json').read_text())['first_fire']['literal'];t,s=base['original_T'],base['original_Tprime'];oldfam=Tree(t).clusters(Tree(t).labels);counts={'reattachments':0,'earlier_admitted':0,'original_selected_still_fails':0,'actual_alternative_pass':0,'conditional_joint_only':0,'unscored':0,'fire':0};rows=[];first=None;clean=[]
 for moving in a.moving:
  assert moving in [0,2];st=Tree(t);strip=st.restriction(st.labels-{moving});foundclean=False
  for address in Tree(strip).child:
   nt=graft(strip,tuple(map(int,address)),moving);counts['reattachments']+=1
   if not selected_valid(nt,s,[7,8]):continue
   counts['earlier_admitted']+=1;w=scan_child(nt,s,[7,8])
   if w is None:continue
   fixed=run_vertex(w);score=Fraction(fixed['minimum_one_paid_full_mass'])
   if score<1:continue
   counts['original_selected_still_fails']+=1;choices=inspect(nt,s);scored=[r for r in choices if r['full_mass'] not in ['CONDITIONAL-JOINT geometry','UNSCORED geometry']];passing=[r for r in scored if Fraction(r['full_mass'])<1];joint=any(r['full_mass']=='CONDITIONAL-JOINT geometry' for r in choices);unscored=any(r['full_mass']=='UNSCORED geometry' for r in choices);best=min(scored,key=lambda r:Fraction(r['full_mass']));isclean=Tree(nt).clusters(Tree(nt).labels)==oldfam
   if isclean:
    assert best['full_mass']=='2729867400/2947295521' and str(score)=='2962867400/2947295521';foundclean=True;clean.append({'moved':moving,'address':address})
   row={'moved':moving,'attachment':address,'selected_mass':str(score),'best':best,'choices':choices,'proper_common_clusters':[sorted(c) for c in (Tree(nt).clusters(st.labels)&Tree(s).clusters(st.labels))-{st.labels}],'clean':isclean}
   counts['actual_alternative_pass']+=bool(passing);counts['conditional_joint_only']+=not passing and joint;counts['unscored']+=unscored
   if not passing and not joint and not unscored:
    counts['fire']+=1
    if first is None:first={'original_T':nt,'original_Tprime':s,'row':row}
   rows.append(row)
  assert foundclean,('missing clean reconstruction',moving)
 out={'controls':ctls,'clean_reconstructions':clean,'moving':a.moving,'counts':counts,'rows':rows,'first_fire':first,'elapsed_seconds':time.perf_counter()-start,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pin_sha256':hashlib.sha256((D/'SPR-PIN-v1.json').read_bytes()).hexdigest(),'scope':'Finite exact weight-certificate selector probe only. No full algorithm/runtime lower bound.'};Path(a.out).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['rows','first_fire','controls']}))
