#!/usr/bin/env python3
"""One-shot source/log adapter for bookkeeping_audit.py, not a Lean verifier.

Checked emitall GUIDE; numeric emission alone cannot recover declaration origin,
source binding, or distinguish compiler diagnostic classes. This adapter reads
exact files and retains a per-file manifest. It does not import author checker
code or run its mathematical enumerator. Small source/diagnostic parser plants
run before real files on every invocation. No external package is required.
"""
import hashlib, json, re, time
from pathlib import Path
from bookkeeping_audit import check
BASE=Path(__file__).resolve().parent
ROOT=BASE.parents[4]
P=ROOT/'research/rmaf/bridge_review/leastness'
MANIFEST={}

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
    p=Path(p)
    MANIFEST[str(p.relative_to(ROOT))]=sha(p)
    return p.read_text()
def obj(p): return json.loads(read(p))

def uncomment(s):
    out=[]; i=0; depth=0
    while i<len(s):
        if s[i:i+2]=='/-': depth+=1; out.extend('  '); i+=2
        elif depth and s[i:i+2]=='-/': depth-=1; out.extend('  '); i+=2
        elif not depth and s[i:i+2]=='--':
            j=s.find('\n',i)
            if j<0: j=len(s)
            out.extend(' '*(j-i)); i=j
        else:
            out.append(s[i] if not depth or s[i]=='\n' else ' '); i+=1
    if depth: raise ValueError('unterminated block comment')
    return ''.join(out)

def declarations(s,namespace,origin):
    rows=[]
    for i,line in enumerate(uncomment(s).splitlines(),1):
        fields=line.strip().split()
        if fields[:1]==['noncomputable']: fields=fields[1:]
        if fields and fields[0] in {'theorem','def'}:
            rows.append({'name':namespace+'.'+fields[1], 'line':i,'kind':fields[0], 'origin':origin,'count_as_new':origin=='local' and fields[0]=='theorem'})
    return rows

def diagnostic(s,code):
    errors=[line for line in s.splitlines() if ': error:' in line]
    if code==0 and not errors: return 'success'
    if len(errors)==1 and errors[0].endswith('error: Tactic `decide` proved that the proposition') and s.rstrip().endswith('\nis false'):
        return 'semantic_falsity'
    if errors and any('error: Type mismatch' in line for line in errors): return 'malformed_proof_failure'
    return 'other_failure'

def axioms(s):
    records={}
    for fragment in s.split("'")[1::2]:
        if not fragment.startswith('LeastEmbedding.'): raise ValueError('unexpected inventory name')
    for entry in re.split(r"(?m)^'",s)[1:]:
        name,body=entry.split("' ",1)
        if name in records: raise ValueError('duplicate inventory entry')
        if body.strip()=='does not depend on any axioms': values=[]
        elif body.startswith('depends on axioms: [') and body.rstrip().endswith(']'):
            values=[v.strip() for v in body.split('[',1)[1].rstrip().removesuffix(']').split(',')]
        else: raise ValueError('unrecognized axiom record')
        records[name]=values
    return records

# Literal plants: expected inventories and outcomes were written by construction.
plant='''namespace Plant
/- theorem phantom : False := by /- nested -/ sorry -/
-- def ignored := 0
def constructor := 0
theorem real : True := True.intro
end Plant
'''
pdecl=declarations(plant,'Plant','local')
assert [(d['name'],d['kind']) for d in pdecl]==[('Plant.constructor','def'),('Plant.real','theorem')]
assert check({'declarations':pdecl,'advertised_new_count':1,'diagnostics':[],'finite_checks':[],'bindings':[]})['accepted']
old=declarations('theorem old : True := True.intro','Old','imported')
assert check({'declarations':old,'advertised_new_count':0,'diagnostics':[],'finite_checks':[],'bindings':[]})['accepted']
old[0]['count_as_new']=True
assert 'imported_as_new' in check({'declarations':old,'advertised_new_count':0,'diagnostics':[],'finite_checks':[],'bindings':[]})['errors']
assert diagnostic('Plant.lean:1:1: error: Tactic `decide` proved that the proposition\n  False\nis false\n',1)=='semantic_falsity'
assert diagnostic('Plant.lean:1:1: error: Type mismatch\n  0\nhas type\n  Nat\nbut is expected to have type\n  True\n',1)=='malformed_proof_failure'
assert diagnostic('',0)=='success'
assert diagnostic('Plant.lean:1:1: error: unknown identifier x\n',1)=='other_failure'
assert axioms("'LeastEmbedding.test' depends on axioms: [propext,\n Quot.sound]\n")=={'LeastEmbedding.test':['propext','Quot.sound']}
assert axioms("'LeastEmbedding.test' does not depend on any axioms\n")=={'LeastEmbedding.test':[]}
fixture=BASE/'hash-plant.txt'; fixture.write_text('known content\n')
known='a5e29604a88ef9dace3ea3de21aa0cfb09946846146070b9a9fe17f2f9701212'
# Expected equality/mismatch here tests the full file-read branch, independently
# of the literal expected/actual branch in the pre-read frozen controls.
# Independently obtained with macOS shasum -a 256, before this comparison.
assert check({'declarations':[],'advertised_new_count':0,'diagnostics':[],'finite_checks':[],'bindings':[{'path':str(fixture),'expected':known}]})['accepted']
assert not check({'declarations':[],'advertised_new_count':0,'diagnostics':[],'finite_checks':[],'bindings':[{'path':str(fixture),'expected':'0'*64}]})['accepted']
(BASE/'adapter-control-receipt.json').write_text(json.dumps({'source_parser_positive':True,'imported_mutant_caught':True,'diagnostic_classes':['semantic_falsity','malformed_proof_failure','success','other_failure'],'axiom_formats':2,'file_hash_positive':True,'file_hash_mismatch_caught':True},indent=2)+'\n')

start=time.monotonic()
c=obj(P/'audit/certificate.json')
report=read(P/'REPORT.md')
assert sha(P/'REPORT.md')=='9ef1c407cb5f32588dfd34814a44dc855ff1e6323f3f08998bbe9c0860b0aa5f'
assert sha(P/'USE-SITE-TRACE.md')=='ac3c9013f25fd4d1d03121b8b3b74137e3bd968a86d9ae5d606cd09ab4b01b6c'
assert sha(P/'audit/REPORT.before-frame-review.md')=='cdefec22bc2d52d70a639754652faeed6a5b15b4895b0a9789a3358dd5d8f163'
assert sha(P/'audit/REPORT.before-wording-review.md')=='8575b723e47abf9c1ae2c2b9eff4270b987b141f7ca9928832f931bf83e2af16'
read(P/'USE-SITE-TRACE.md'); obj(P/'INDEPENDENCE.json')
bindings=[]
for path,expected in c['source_hashes'].items():
    read(ROOT/path); bindings.append({'path':str(ROOT/path),'expected':expected})
assert check({'declarations':[],'advertised_new_count':0,'diagnostics':[],'finite_checks':[],'bindings':bindings})['accepted'], 'Source mismatch invalidates certificate'
module_paths={
    'TreeAddresses':P/'address_semantics/TreeAddresses.lean',
    'ExtractorLeastness':P/'lean/ExtractorLeastness.lean',
    'ActualEmbedding':P/'lean/ActualEmbedding.lean',
    'LeastnessControls':P/'lean/LeastnessControls.lean'}
decls=[]; counts={}
for name,path in module_paths.items():
    namespace='LeastEmbedding.Controls' if name=='LeastnessControls' else 'LeastEmbedding'
    rows=declarations(read(path),namespace,'local')
    for row in rows: row['source']=str(path.relative_to(ROOT))
    decls.extend(rows)
    counts[name]={'theorems':sum(r['kind']=='theorem' for r in rows),'definitions':sum(r['kind']=='def' for r in rows)}
assert counts==c['module_counts']
assert sum(x['theorems'] for x in counts.values())==66==c['new_theorem_count']
assert sum(x['definitions'] for x in counts.values())==9==c['new_definition_count']
assert '66 named new theorems: 22 semantic, 13 extractor, 7 constructor/interface and' in report
assert '24 control theorems.' in report
assert '9 definitions: all 75 reports' in report
raw_axioms=read(ROOT/c['builds']['AxiomAudit']['log'])
parsed_axioms=axioms(raw_axioms)
assert parsed_axioms==c['axioms']
assert set(parsed_axioms)=={r['name'] for r in decls}
assert len(parsed_axioms)==75==c['new_axiom_report_count']
assert all(set(v)<={'propext','Quot.sound','Classical.choice'} for v in parsed_axioms.values())
oldpaths=[ROOT/'research/rmaf/lean/RMAF.lean',ROOT/'research/rmaf/pure_bridge/lean/PureBridge.lean',ROOT/'research/rmaf/bridge_review/lean/GraphRegion.lean',ROOT/'research/rmaf/bridge_review/executable/lean/ExecutableConnectivity.lean']
for path in oldpaths:
    decls.extend(declarations(read(path),path.stem,'imported'))
for path in oldpaths+list(module_paths.values()):
    source=uncomment(read(path))
    assert not re.search(r'\b(sorry|admit|native_decide|unsafe|axiom)\b',source)
log_checks=[]
for name,entry in c['builds'].items():
    log=read(ROOT/entry['log']); bindings.append({'path':str(ROOT/entry['log']),'expected':entry['log_sha256']})
    assert diagnostic(log,entry['exit_code'])=='success'
    log_checks.append({'name':name,'class':'success'})
for name,entry in c['false_controls'].items():
    log=read(ROOT/entry['log']); bindings.append({'path':str(ROOT/entry['log']),'expected':entry['log_sha256']})
    assert diagnostic(log,entry['exit_code'])=='semantic_falsity'
    log_checks.append({'name':name,'class':'semantic_falsity'})
for key,want in [('malformed_diagnostic_control','malformed_proof_failure'),('clean_diagnostic_twin','success')]:
    entry=c[key]; log=read(ROOT/entry['log']); bindings.append({'path':str(ROOT/entry['log']),'expected':entry['log_sha256']})
    assert diagnostic(log,entry['exit_code'])==want
    log_checks.append({'name':key,'class':want})
assert len(c['false_controls'])==5
assert len(c['parser_controls'])==6 and all(v['actual']==v['expected'] for v in c['parser_controls'].values())
assert sha(P/'CONTROLS.json')==read(P/'controls.sha256').split()[0]
frozen=obj(P/'CONTROLS.json')
expected_values={case['name']+'_'+kind:case[kind] for case in frozen['cases'] for kind in ['terminals','support']}
assert len(frozen['cases'])==9 and len(expected_values)==18
def literal_fixture_values(source):
    values={}
    for line in source.splitlines():
        if line.startswith('theorem ') and ' := by decide' in line:
            name=line.split()[1]
            if name in expected_values:
                values[name]=json.loads(line.split(' = ',1)[1].split(' := by decide',1)[0])
    return values
assert literal_fixture_values(read(P/'lean/LeastnessControls.lean'))==expected_values
assert literal_fixture_values(read(P/'audit/LeastnessControls.attempt1.lean'))==expected_values

adv=P/'adversary'; a=obj(adv/'results/final-report.json')
for path,expected in a['files'].items():
    # Binary files enter the manifest without text decoding.
    full=adv/path; MANIFEST[str(full.relative_to(ROOT))]=sha(full)
    bindings.append({'path':str(full),'expected':expected})
b=obj(adv/'results/bound4.json'); lc=obj(adv/'results/lean-checks.json')
assert b['cases']==sum(x['cases'] for x in b['bounds'])==816
assert sum(x['subsets_examined'] for x in b['bounds'])==85488
assert b['pilot']['fixture_count']==10 and len(b['pilot']['fixtures'])==10
assert b['pilot']['caught_corruptions']==5==b['pilot']['true_twins']
assert lc['finite_source_equalities']==826
finite_decls=[]
for fn in ['FrozenFixtures.lean','GraphCorpus.lean']:
    rows=declarations(read(adv/'lean'/fn),'Finite','imported')
    finite_decls.extend(rows)
assert sum(r['kind']=='theorem' for r in finite_decls)==826
for run in lc['runs']:
    log=read(Path(run['log'])); src=Path(run['command'][-1])
    bindings.extend([{'path':str(src),'expected':run['source_sha256']},{'path':run['log'],'expected':run['output_sha256']}])
    want='malformed_proof_failure' if run['id']=='MalformedProof' else ('semantic_falsity' if run['id'].startswith('Semantic') else 'success')
    assert diagnostic(log,run['returncode'])==want
assert 'These finite checks cannot prove the' in report
normalized={'declarations':decls,'advertised_new_count':66,'diagnostics':[{'result':'malformed_proof_failure','claim':'diagnostic_only'}],'finite_checks':[{'claim':'finite_only'}],'bindings':bindings}
(BASE/'normalized-real-input.json').write_text(json.dumps(normalized,indent=2)+'\n')
verdict=check(normalized)
result={'status':'passed' if verdict['accepted'] else 'failed','scope':'Source/log/claim bookkeeping; no mathematical enumeration or independent universal proof','new_module_counts':counts,'new_theorems':66,'new_definitions':9,'axiom_reports':75,'frozen_literal_fixture_values':len(expected_values),'fixture_values_unchanged_from_failed_attempt':True,'imported_declarations_excluded':sum(d['origin']=='imported' for d in decls),'source_and_log_bindings':len(bindings),'author_diagnostics':log_checks,'finite_receipt_claims':{'corpus_cases':b['cases'],'corpus_subsets':sum(x['subsets_examined'] for x in b['bounds']),'fixture_cases':10,'source_equalities':lc['finite_source_equalities']},'bookkeeping':verdict,'manifest':MANIFEST,'script_sha256':sha(Path(__file__)),'elapsed_seconds':time.monotonic()-start,'not_run':['Lean rebuild (owned by fresh mathematical review)','mathematical enumerator','project-wide bootloops-check','novelty review']}
(BASE/'receipt-verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in {'manifest','author_diagnostics'}}))
if not verdict['accepted']: raise SystemExit(1)
