"""Compare author decisions to the already frozen fresh partition instrument.
Post-unblinding candidate import allowed; no author oracle/helper import.
"""
import argparse, importlib.util, json, random, time, hashlib
from pathlib import Path
from independent import Graph, trees, optimum_partition, controls
HERE=Path(__file__).parent; TARGET=HERE.parent/'thesis_correctness'/'algorithm.py'
spec=importlib.util.spec_from_file_location('candidate_algorithm',TARGET)
candidate=importlib.util.module_from_spec(spec)
import sys
sys.modules[spec.name]=candidate;spec.loader.exec_module(candidate)

def run(pairs,tag):
 start=time.perf_counter();stats={}; failures=[];done=0;budgets=0
 for t1,t2 in pairs:
  g,h=Graph([t1],True),Graph([t2],True); q=optimum_partition(g,h)-1
  for b in range(-1,q+2):
   try: actual=candidate.decide(t1,t2,b,stats)
   except Exception as e: failures.append({'t1':t1,'t2':t2,'budget':b,'q':q,'exception':repr(e)});break
   budgets+=1
   if actual!=(b>=q): failures.append({'t1':t1,'t2':t2,'budget':b,'q':q,'actual':actual});break
  if failures:break
  done+=1
 return {'tag':tag,'pairs':done,'expected_pairs':len(pairs),'budgets':budgets,'stats':stats,'failures':failures,'seconds':time.perf_counter()-start}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--pilot',action='store_true');ap.add_argument('--full',action='store_true');a=ap.parse_args()
 control=controls(); reports=[];rng=random.Random(6142026)
 for n,count in ([(4,225),(5,10),(6,10)] if a.pilot else [(4,225),(5,150),(6,150)]):
  ts=trees(list('abcdef'[:n]));ids=list(range(len(ts)**2)) if n==4 else rng.sample(range(len(ts)**2),count)
  reports.append(run([(ts[i//len(ts)],ts[i%len(ts)]) for i in ids],f'n{n}'))
  if reports[-1]['failures']: break
 # Author-selected examples add branch coverage, not independent sampling.
 if a.full:
  p=HERE.parent/'results'/'thesis-correctness-sweep-n6-limit3000-seed613.json'
  witnesses=json.loads(p.read_text())['branch_witnesses']
  reports.append(run([(w['t1'],w['t2']) for w in witnesses.values()],'author_branch_witnesses'))
 receipt={'candidate_sha256':hashlib.sha256(TARGET.read_bytes()).hexdigest(),'reference_sha256':hashlib.sha256((HERE/'independent.py').read_bytes()).hexdigest(),'controls':len(control),'seed':6142026,'scope':'fresh oracle against author decisions; finite only','reports':reports}
 path=HERE/('candidate-pilot.json' if a.pilot else 'candidate-full.json');path.write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(reports))
 assert not any(r['failures'] for r in reports)
if __name__=='__main__':main()
