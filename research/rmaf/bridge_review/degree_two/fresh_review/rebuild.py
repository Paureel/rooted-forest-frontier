"""One-shot fresh source-copy Lean replay and axiom/source/log audit.
All generated files remain in fresh_review; never executes author audit scripts.
Controls: matching hash passes; altered expected digest, altered bytes, missing
file must fail. Every positive source must compile; negative propositions must
fail specifically because the proposition is false, not elaboration damage.
"""
from pathlib import Path
import os, re, json, hashlib, subprocess, time, datetime
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
DEG=ROOT/'research/rmaf/bridge_review/degree_two'
BUILD=HERE/'build_initial'
BUILD.mkdir(exist_ok=True)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def same_pin(p,h): return p.is_file() and sha(p)==h
# Before audit: demonstrate comparator rejection and positive twin.
a=HERE/'hash_positive.txt'; a.write_text('source-control\n')
h=sha(a)
assert same_pin(a,h)
assert not same_pin(a,'0'*64)
a.write_text('corrupted-source-control\n')
assert not same_pin(a,h)
assert not same_pin(HERE/'does-not-exist',h)
receipt={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'hash_controls':['positive accepted','wrong digest rejected','changed bytes rejected','missing file rejected'],
         'builds':[], 'controls':[], 'pin_checks':[], 'declarations':[]}
def save(): (HERE/'rebuild_initial_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
base=['research/rmaf/lean/RMAF.lean','research/rmaf/pure_bridge/lean/PureBridge.lean',
'research/rmaf/bridge_review/lean/GraphRegion.lean',
'research/rmaf/bridge_review/executable/lean/ExecutableConnectivity.lean',
'research/rmaf/bridge_review/leastness/address_semantics/TreeAddresses.lean',
'research/rmaf/bridge_review/leastness/lean/ExtractorLeastness.lean',
'research/rmaf/bridge_review/leastness/lean/ActualEmbedding.lean']
more=['graph_route/lean/DegreePropagation.lean','lean/PartitionRefinement.lean',
'lean/ConsumerControls.lean','lean/LocalSplit.lean','lean/DegreeCounting.lean',
'lean/LocalSplitControls.lean','lean/AgreementBlock.lean',
'graph_route/lean/GraphRouteControls.lean','graph_route/lean/DegreePropagationControls.lean']
sources=[ROOT/x for x in base]+[DEG/x for x in more]
accepted=json.loads((ROOT/'research/rmaf/bridge_review/leastness/acceptance.json').read_text())['source_hashes']
# Verify all completed core input pins, without reading unfinished routes.
for p in sources[:len(base)]:
    r=str(p.relative_to(ROOT)); good=same_pin(p,accepted[r]); receipt['pin_checks'].append({'path':r,'expected':accepted[r],'actual':sha(p),'pass':good}); assert good
# Inspect binding in author receipts, not their asserted conclusions.
for receipt_path in [DEG/'graph_route/formal-receipt.json', DEG/'audit/one-tree-checkpoint-receipt.json', DEG/'audit/consumer-receipt.json']:
    d=json.loads(receipt_path.read_text())
    rows=d.get('results',[])+d.get('builds',[])+d.get('source_declarations',[])
    rows += [dict(row,source=str((DEG/'lean'/('CleanTwin.lean' if name=='CleanTwin' else ('malformed/'+name+'.lean' if name=='WrongType' else 'negative/'+name+'.lean'))).relative_to(ROOT))) for name,row in d.get('diagnostics',{}).items()]
    if 'axiom_log' in d: rows.append({'log':d['axiom_log'],'log_sha256':d['axiom_log_sha256']})
    if 'script' in d: rows.append({'source':d['script'],'source_sha256':d['script_sha256']})
    for row in rows:
        for field,hashfield in [('source','source_sha256'),('source','sha256'),('log','log_sha256')]:
            if field in row and hashfield in row:
                p=ROOT/row[field]; good=same_pin(p,row[hashfield])
                receipt['pin_checks'].append({'receipt':str(receipt_path.relative_to(ROOT)),'path':row[field],'expected':row[hashfield],'actual':sha(p) if p.is_file() else None,'pass':good})
                assert good, ('STALE_AUTHOR_PIN',row[field])
# Snapshot all sources before compiling to avoid mixed live versions.
for p in sources:
    q=BUILD/p.name; q.write_bytes(p.read_bytes())
    receipt['declarations'].extend([])
env=os.environ.copy(); env['LEAN_PATH']=str(BUILD)
allowed={'propext','Classical.choice','Quot.sound'}
def run(p,name,positive=True,semantic=False):
    start=time.perf_counter(); log=BUILD/(name+'.log')
    cmd=[str(ROOT/'bootloops-lean')]
    if positive: cmd += ['-o',str(BUILD/(name+'.olean'))]
    cmd += [str(p)]
    r=subprocess.run(cmd,cwd=ROOT,env=env,text=True,capture_output=True,timeout=60)
    s=r.stdout+r.stderr; log.write_text(s)
    row={'source':str(p.relative_to(ROOT)), 'sha256':sha(p), 'exit_code':r.returncode,
         'elapsed_seconds':time.perf_counter()-start,'log':str(log.relative_to(ROOT)),'log_sha256':sha(log)}
    if semantic:
        row['semantic_falsity']=r.returncode!=0 and 'is false' in s and 'type mismatch' not in s.lower() and 'unknown identifier' not in s.lower() and 'unexpected token' not in s.lower()
        assert row['semantic_falsity'],row
    elif positive: assert r.returncode==0 and 'sorryAx' not in s,row
    else:
        row['diagnostic_only']=r.returncode!=0 and 'is false' not in s
        assert row['diagnostic_only'],row
    return row
for i,p in enumerate(sources):
    q=BUILD/p.name
    row=run(q,p.stem)
    row.update({'original_source':str(p.relative_to(ROOT)),'original_sha256':sha(p),'snapshot_matches':sha(p)==sha(q)})
    assert row['snapshot_matches']
    receipt['builds'].append(row); save()
    if i==0:
        receipt['pilot_timing']={'module':p.stem,'elapsed_seconds':row['elapsed_seconds'],'remaining_source_modules':len(sources)-1,'policy':'bounded source rebuild only; per-module timeout 60 seconds; no census expansion'}
# Discover named declarations from comment-stripped pinned bytes, not author counts.
# Scope includes dependencies and all released modules, with the module retained.
def uncomment(s):
    out=[]; i=0; depth=0
    while i<len(s):
        if s[i:i+2]=='/-': depth+=1; i+=2
        elif depth and s[i:i+2]=='-/': depth-=1; i+=2
        elif not depth and s[i:i+2]=='--':
            end=s.find('\n',i); i=len(s) if end<0 else end
        else:
            out.append(s[i] if not depth or s[i]=='\n' else ' '); i+=1
    assert depth==0
    return ''.join(out)
names=[]
for p in sources:
    text=uncomment((BUILD/p.name).read_text()); ns=[]
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',text)
    for line_no,line in enumerate(text.splitlines(),1):
        m=re.match(r'^namespace\s+([\w.]+)',line)
        if m: ns.append(m[1]); continue
        if re.match(r'^end(?:\s+\S+)?\s*$',line):
            if ns: ns.pop()
            continue
        m=re.match(r'^(?:(?:noncomputable|private|protected)\s+)*(def|abbrev|theorem|lemma|inductive|structure)\s+([\w.]+)',line)
        if m:
            kind,name=m.groups(); qualified='.'.join(ns+[name]); names.append(qualified)
            receipt['declarations'].append({'module':p.stem,'name':qualified,'kind':kind,'source':str(p.relative_to(ROOT)),'line':line_no})
assert len(names)==len(set(names)), 'duplicate qualified names'
ax=BUILD/'FreshAxioms.lean'; ax.write_text('\n'.join('import '+p.stem for p in sources)+'\n\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
row=run(ax,'FreshAxioms'); receipt['axiom_build']=row
s=(BUILD/'FreshAxioms.log').read_text()
reports={}
for name,deps in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",s,re.S):
    aa={x.strip() for x in deps.replace('\n',' ').split(',') if x.strip()}; assert aa<=allowed,(name,aa); reports[name]=sorted(aa)
for name in re.findall(r"'([^']+)' does not depend on any axioms",s): reports[name]=[]
assert set(names)==set(reports), {'missing':set(names)-set(reports),'extra':set(reports)-set(names)}
receipt['axiom_reports']=reports
for directory,prefix in [(DEG/'graph_route/lean/negative','GraphFalse'),(DEG/'lean/negative','ConsumerFalse')]:
    for p in sorted(directory.glob('*.lean')):
        q=BUILD/(prefix+p.stem+'.lean'); q.write_bytes(p.read_bytes())
        row=run(q,q.stem,positive=False,semantic=True); row['original_source']=str(p.relative_to(ROOT)); receipt['controls'].append(row); save()
for relative,positive in [('lean/CleanTwin.lean',True),('lean/malformed/WrongType.lean',False)]:
    p=DEG/relative; q=BUILD/p.name; q.write_bytes(p.read_bytes())
    receipt['controls'].append(run(q,q.stem,positive=positive)); save()
receipt['status']='PASS_SCOPED_REBUILD_AND_CONTROLS'
receipt['source_hashes']={str(p.relative_to(ROOT)):sha(p) for p in sources}
receipt['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat(); save()
print(json.dumps({'status':receipt['status'],'source_modules':len(sources),'all_named_declarations_audited':True,'semantic_controls':sum(x.get('semantic_falsity',False) for x in receipt['controls']),'diagnostic_malformed_excluded':True}))
