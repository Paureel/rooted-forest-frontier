"""Package executed review evidence, reproduce source fixtures, replay clean Lean.
This one-shot reporter checks source hashes and fails if any required receipt is absent.
It does not promote finite checks into universal claims.
"""
import hashlib,json,os,re,subprocess
from pathlib import Path
from independent import Graph,optimum_partition
HERE=Path(__file__).resolve().parent;RMAF=HERE.parent;WORK=RMAF.parent.parent
TARGET=RMAF/'thesis_correctness';RES=RMAF/'results';LEANDIR=HERE/'lean-isolated'
def read(p):return json.loads(p.read_text())
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()

# Compare the source files actually reviewed with the author's frozen summary.
author=read(RES/'thesis-correctness-summary.json')
hashes={p:(digest(Path(p))==h) for p,h in author['source_hashes'].items()}
assert all(hashes.values()),hashes
original_receipts=[]
for n,limit in [(4,0),(5,0),(6,3000)]:
 p=RES/f'thesis-correctness-sweep-n{n}-limit{limit}-seed613.json';z=read(p)
 assert z['pass'] and z['denominator_complete'] and not z['failures']
 for name,h in z['hashes'].items(): assert digest(TARGET/name)==h,(p,name)
 original_receipts.append({'file':str(p.relative_to(WORK)),'pairs':z['completed'],'hashes_match':True,'meaning':'author receipt inspected, not independently rerun in full'})
assert sum(r['pairs'] for r in original_receipts)==author['current_implementation_pairs']

# Rebuild the author's four fixed controls using only the reviewer's graph route.
ctl=[]
for z in read(TARGET/'controls.json')['known_answers']:
 got=optimum_partition(Graph([z['t1']],True),Graph([z['t2']],True))-1
 assert got==z['optimum_cuts'];ctl.append({'id':z['id'],'expected':z['optimum_cuts'],'fresh_partition_cuts':got})
# The exact author root fixture, now freshly reconstructed without author helpers.
g=Graph([(('a','c'),'b')],True);h=Graph([(('a','b'),'c'),'rho']);gm=g.allcuts()
E={h.bylabel[x] for x in 'abc'};E0={h.bylabel['b']}
root={'source':'SEMANTICS.md root-safe normalization fixture','original_cut_AF':h.cut(E) in gm,'root_safe_normalized_AF':h.cut(E0) in gm,'LCA_parent_absent':0 not in h.parent}
assert all(root[k] for k in ['original_cut_AF','root_safe_normalized_AF','LCA_parent_absent'])
# Standalone Lemma6.3: compatible triples and nonoverlap alone fail containment.
f=Graph(['rho','a']);k=Graph(['a'],True)
lemma63={'labels':2,'target_components':1,'triples':0,'component_overlap':False,'forest_refinement':k.cut([]) in f.allcuts()}
assert not lemma63['forest_refinement']

# Clean dependency replay: only Std imports, fresh copied source, LEAN_PATH unset.
assert (LEANDIR/'ProtectedBranch.lean').read_bytes()==(TARGET/'ProtectedBranch.lean').read_bytes()
env=os.environ.copy();env.pop('LEAN_PATH',None)
lean=[]
for name,expect in [('ProtectedBranch',0),('PositiveTwin',0),('OriginalNegativeControl',1),('ExistentialRepair',0)]:
 p=subprocess.run([str(WORK/'bootloops-lean'),name+'.lean'],cwd=LEANDIR,env=env,text=True,capture_output=True)
 log=LEANDIR/(name+'-replay.log');log.write_text(p.stdout+p.stderr)
 assert p.returncode==expect,(name,p.returncode,p.stdout,p.stderr)
 if expect:assert 'proved that the proposition' in p.stdout and 'is false' in p.stdout
 lean.append({'file':name+'.lean','exit_code':p.returncode,'log':str(log.relative_to(WORK))})
axiom_log=(LEANDIR/'ProtectedBranch-replay.log').read_text()
assert axiom_log.count('depends on axioms:')==3 and axiom_log.count('does not depend on any axioms')==4
for ax in re.findall(r'depends on axioms: \[([^\]]*)\]',axiom_log):assert set(ax.split(', '))<={'propext','Quot.sound'}
assert (LEANDIR/'ExistentialRepair-replay.log').read_text().count('does not depend on any axioms')==3

ind=read(HERE/'independent-full.json');cand=read(HERE/'candidate-full.json');state=read(HERE/'state-audit-120.json');cov=read(HERE/'cover-adversary.json');domain=read(HERE/'normalization-domain.json')
assert not any(z['failures'] for z in ind['census']) and not any(z['failures'] for z in cand['reports'])
assert cov['counterexamples']>0 and domain['E_yields_AF'] and not domain['E0_yields_AF']
summary={
 'id':'thesis-correctness-review','status':'open','verdict':'Narrow executable and Lean results corroborated; two concrete proof-interface/domain findings retained.',
 'universal_correctness':'OPEN','algorithm_decision_counterexample_found':False,
 'independent_frozen_controls':len(ind['controls']),'independent_cut_partition_pairs':sum(z['pairs'] for z in ind['census']),
 'independent_A2BC_exchange_premises':sum(z['A2BC_exchange_premises'] for z in ind['census']),
 'candidate_pairs':sum(z['pairs'] for z in cand['reports']),'candidate_budget_decisions':sum(z['budgets'] for z in cand['reports']),
 'candidate_mismatches':0,'fresh_sample_seed':cand['seed'],'all_n4_pairs':225,'sample_n5':150,'sample_n6':150,'author_selected_witness_pairs':9,
 'candidate_cases_reached':sorted({k for z in cand['reports'] for k in z['stats']} & {'AC','B','RB','RB*','2B','BCY','A2BC','A2BC-protected-c','A3BC'}),
 'actual_state_audit':{'states':state['states'],**state['totals']},
 'source_fixture_reconstruction':{'author_controls':ctl,'root_safe_fixture':root,'Lemma6_3':lemma63},
 'lean':{'original_theorems':7,'original_axiom_union':['propext','Quot.sound'],'true_twin_passed':True,'false_twin_rejected_for_mathematical_falsity':True,'review_existential_repair_theorems':3,'repair_axioms':[], 'replays':lean},
 'findings':[
 {'id':'RAW-COVER','severity':'high-for-universal-proof-interface','status':'refuted_as_raw_optimum_coverage','claim':'Every minimum original-edge cutset contains A, BB, or C','counterexample_file':'research/rmaf/thesis_correctness_review/cover-adversary.json','consequence':'Use existential branch coverage plus child-membership exclusion, or justify a normalized optimal family. Original conditional Lean theorems remain valid.'},
 {'id':'NORMALIZATION-DOMAIN','severity':'medium','status':'refuted_on_literal_standalone_domain','claim':'Root-safe Lemma6.5 follows from its printed standalone hypotheses alone','counterexample_file':'research/rmaf/thesis_correctness_review/normalization-domain.json','consequence':'Carry active F2-to-F1 component containment / AF compatibility. Witness violates that active invariant and is not an algorithm counterexample.'}],
 'remaining_obligations':['Root-safe normalization AF preservation for valid active states','Original-edge and optimum transport through suppression and common-subtree contraction','Source structural branch coverage and a correct quantifier interface','Marked-state induction or coupling for protection-dependent selection and order','Finishing, termination, and full soundness/completeness composition'],
 'limits':['Only finite exact graph checks; no universal graph theorem proved','Root-safe formula tested on constructed fixtures; no root-normalization premise occurred in 120 sampled snapshots','Original 14250-pair census receipts and hashes inspected, not rerun in full by reviewer','No complexity, convention transfer, or novelty claim','No complexity/transfer agent work read','Toolkit-wide validation not rerun because upstream toolkit code was unchanged'],
 'author_receipts_inspected':original_receipts,'author_source_hashes_match':hashes,
 'provenance':{'freeze':'research/rmaf/thesis_correctness_review/independent-freeze.sha256','journal':'research/rmaf/thesis_correctness_review/WORKFILE.md','independent_source_sha256':digest(HERE/'independent.py'),'candidate_sha256':digest(TARGET/'algorithm.py')}
}
(RES/'thesis-correctness-review-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['status','candidate_pairs','candidate_budget_decisions','candidate_mismatches','independent_cut_partition_pairs','findings']}))
