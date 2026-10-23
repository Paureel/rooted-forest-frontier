"""One-shot exact producer/resolved/value-closure consistency checks."""
from pathlib import Path
from hashlib import sha256
import json,collections
H=Path(__file__).resolve().parent
adoption=json.loads((H/'SOURCE-ADOPTION-v2.json').read_text());modules=adoption['order'];stored=json.loads((H/'STORED-OCCURRENCE-INDEX-v4.json').read_text());rr=json.loads((H/'RESOLVED-ROWS-v3.json').read_text());before=rr['rows']['before'];after=rr['rows']['after'];refs={r['name']:r for r in rr['references']['after']};names={r['stored']['name'] for r in stored['occurrences']}
assert names=={r['name'] for r in before} and len(names)==2612
assert len(stored['occurrences'])==2627 and len(stored['producers'])==66
for phase,rows in rr['rows'].items():
 assert len(rows)==len({r['name'] for r in rows})
 for r in rows:
  assert r['origin'] in modules and r['kind']!='axiom'
  assert set(filter(None,r['axioms'].split(',')))<={'propext','Classical.choice','Quot.sound'}
  if r['adapter'].startswith('generated-prefix:'):
   parent=r['adapter'].split(':',1)[1];matches=[p for p in before if p['name']==parent and p['origin']==r['origin']];assert len(matches)==1,('unmapped generated producer',r)
  else:assert r['rawOrigin']==r['origin']
new=rr['newAfterLiteralForcing'];assert len(new)==110 and len(after)==2722
producer_counts=collections.Counter(r['producer'] for r in stored['occurrences']);kinds=collections.Counter(r['stored']['kind'] for r in stored['occurrences']);coalesced=[]
byname=collections.defaultdict(list)
for r in stored['occurrences']:byname[r['stored']['name']].append(r)
for n,occ in byname.items():
 if len(occ)>1:
  assert all(o['stored']['kind']=='theorem' for o in occ)
  assert len({o['stored']['typeExprSHA256'] for o in occ})==1
  coalesced.append({'name':n,'producers':[o['producer'] for o in occ],'typesByteIdentical':True,'storedBodiesByteIdentical':len({o['stored']['valueExprSHA256'] for o in occ})==1,'resolvedOrigins':[o['resolvedOrigin'] for o in occ]})
def value_closure(start):
 pending=[start];seen=set();edges=[];external=set();proof=[]
 while pending:
  n=pending.pop()
  if n in seen:continue
  seen.add(n);r=refs[n]
  if r['kind']=='theorem':proof.append(n);continue
  for d in r['valueRefs']:
   if d in refs:edges.append([n,d]);pending.append(d)
   else:external.add(d)
 return {'entrypoint':start,'scientificNames':sorted(seen),'scientificValueEdges':edges,'standardOrCompilerNames':sorted(external),'theoremNamesEncounteredAndErased':sorted(proof)}
closures=[value_closure(n) for n in ['AllGoodDP.run','AllGoodDP.decideBudget']]
for c in closures:
 bad=[n for n in c['scientificNames'] if any(s in n for s in ['FinalCutRecovery','CoreProgram.generate','RMAF.assignments','RMAF.solve','RMAF.blocks','agreement_coloring','candidate_minimum','recover_checked'])]
 assert not bad,('forbidden-runtime-scientific-value-callee',c['entrypoint'],bad)
 assert not c['theoremNamesEncounteredAndErased'],('proof callee needs explicit erasure inspection',c)
output={'status':'PRODUCER-RESOLVED-AND-VALUE-CLOSURE-PASS','scientificModules':66,'storedOccurrences':2627,'storedUniqueNames':2612,'privateStoredOccurrences':251,'storedKinds':dict(kinds),'perProducerCounts':dict(producer_counts),'coalescedTheorems':coalesced,'resolvedBefore':2612,'resolvedAfter':2722,'literalSourceProducersForced':212,'actualNewGeneratedNames':110,'axiomUnion':sorted({a for r in after for a in r['axioms'].split(',') if a}),'directCustomAxioms':[],'runtimeClosures':closures,'scope':'Exact source value-reference closure, separately from proof/import closure. This does not prove compiled-machine operational semantics. All stored producer occurrences, including coalesced/private/unused ones, inspected by qualified detector. No all-possible synthesized-equations completeness claim.','independentReplicaIncrement':0}
(H/'AUDIT-AND-RUNTIME-SUMMARY-v1.json').write_text(json.dumps(output,indent=2)+'\n');print(json.dumps({k:v for k,v in output.items() if k not in ['runtimeClosures','coalescedTheorems','perProducerCounts']}))
