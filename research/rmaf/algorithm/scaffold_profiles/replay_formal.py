"""One-shot source-bound author replay for this arm's exact Lean claims.
It is not fresh-context mathematical review or independent verification.
"""
from pathlib import Path
import subprocess,time,hashlib,json,re,os
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'research/rmaf/algorithm/scaffold_profiles';L=BASE/'lean';S=L/'source'
OUT=ROOT/'research/rmaf/results/algorithm-scaffold-profiles-formal-receipt-v1.json'
if OUT.exists():raise FileExistsError(OUT)
start=time.perf_counter();rows=[]
for name in ('RMAF','CoreGraph','CoreProgram','SourceCompression'):
    path=S/(name+'.lean');cmd=[str(ROOT/'bootloops-lean'),'-o',str(S/(name+'.olean')),str(path)]
    env=dict(os.environ,LEAN_PATH=str(S));t=time.perf_counter();p=subprocess.run(cmd,cwd=ROOT,env=env,capture_output=True,text=True)
    log=S/(name+'-replay.log');log.write_text(p.stdout+p.stderr);assert p.returncode==0,(name,log)
    rows.append({'module':name,'exit':p.returncode,'seconds':time.perf_counter()-t,'log':str(log.relative_to(ROOT))})
p=L/'Profiles.lean';t=time.perf_counter();r=subprocess.run([str(ROOT/'bootloops-lean'),'-o',str(L/'Profiles.olean'),str(p)],cwd=ROOT,capture_output=True,text=True)
log=L/'Profiles-replay.log';log.write_text(r.stdout+r.stderr);assert r.returncode==0
rows.append({'module':'Profiles','exit':r.returncode,'seconds':time.perf_counter()-t,'log':str(log.relative_to(ROOT))})
new={}
allowed={'propext','Classical.choice','Quot.sound'}
for p,log in [(L/'Profiles.lean',L/'Profiles-replay.log'),(S/'SourceCompression.lean',S/'SourceCompression-replay.log')]:
    src=p.read_text();assert not re.search(r'\b(sorry|admit|native_decide)\b|(?m:^\s*axiom\b)',src)
    expected=re.findall(r'(?m)^theorem\s+(\w+)',src);observed={}
    for line in log.read_text().splitlines():
        m=re.match(r"'([^']+)' (.*)",line)
        if not m:continue
        name=m[1].split('.')[-1]
        if name not in expected:continue
        tail=m[2]
        ax=set(re.findall(r'\b(?:propext|Classical\.choice|Quot\.sound|sorryAx)\b',tail))
        assert 'sorryAx' not in ax
        if 'depends on axioms:' in tail:
            raw=tail.split('[',1)[1].split(']',1)[0]
            names={x.strip() for x in raw.split(',') if x.strip()};assert names<=allowed,(name,names);ax=names
        else:assert 'does not depend on any axioms' in tail,(name,tail)
        observed[name]=sorted(ax)
    assert set(expected)==set(observed),(expected,observed)
    new[str(p.relative_to(ROOT))]=observed
negative=[]
for p in (L/'FalseBalanced.lean',L/'FalseRawProgress.lean',L/'FalseExchangeThree.lean',S/'FalseTerminal.lean'):
    t=time.perf_counter();r=subprocess.run([str(ROOT/'bootloops-lean'),str(p)],cwd=ROOT,env=dict(os.environ,LEAN_PATH=str(S)),capture_output=True,text=True)
    log=p.with_name(p.stem+'-replay.log');txt=r.stdout+r.stderr;log.write_text(txt)
    assert r.returncode!=0 and 'proved that the proposition' in txt and 'is false' in txt,(p,txt)
    negative.append({'file':str(p.relative_to(ROOT)),'exit':r.returncode,'seconds':time.perf_counter()-t,'rejected_as_false':True,'log':str(log.relative_to(ROOT))})
files=[L/'Profiles.lean',S/'SourceCompression.lean',S/'RMAF.lean',S/'CoreGraph.lean',S/'CoreProgram.lean',Path(__file__)]
upstream={S/'RMAF.lean':ROOT/'research/rmaf/lean/RMAF.lean',S/'CoreGraph.lean':ROOT/'research/rmaf/algorithm/universal233/core/CoreGraph.lean',S/'CoreProgram.lean':ROOT/'research/rmaf/algorithm/universal233/core/CoreProgram.lean'}
match={str(copy.relative_to(ROOT)):copy.read_bytes()==src.read_bytes() for copy,src in upstream.items()};assert all(match.values())
result={'scope':'Source-bound AUTHOR replay; independent review and structural/source interfaces remain OPEN','positive_builds':rows,'new_theorem_count':sum(map(len,new.values())),'complete_new_axiom_audits':new,'false_controls':negative,'exact_upstream_source_copies':match,
 'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},'seconds':time.perf_counter()-start}
OUT.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'builds':len(rows),'new_theorems':result['new_theorem_count'],'false_controls':len(negative),'seconds':result['seconds'],'receipt':str(OUT)}))
