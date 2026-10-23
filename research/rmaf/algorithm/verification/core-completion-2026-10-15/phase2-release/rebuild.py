"""Independent isolated source rebuild and full-origin audit (standard library).

Input membership is taken from the two released hash manifests/certificates;
the build/audit implementation is written here, not imported from either author.
Never copies a compiled file. Logs, including failed experiments, are retained.
"""
from pathlib import Path
import hashlib, json, os, re, subprocess, time, sys

ROOT = Path(__file__).resolve().parents[6]
HERE = Path(__file__).resolve().parent
LEAN = ROOT / 'bootloops-lean'
ALLOW = {'propext', 'Quot.sound', 'Classical.choice'}

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def run(build, module, args=()):
    env = os.environ.copy(); env['LEAN_PATH'] = str(build)
    start = time.monotonic()
    p = subprocess.run([str(LEAN), *args, f'{module}.lean'], cwd=build,
                       env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = build / f'{module}.log'; log.write_bytes(p.stdout)
    return {'module':module, 'exit':p.returncode, 'seconds':time.monotonic()-start,
            'log':str(log.relative_to(ROOT)), 'log_sha256':digest(log)}

def audit_text(modules, top):
    # Origin-index membership rather than public names or namespaces is crucial:
    # it includes private constants, equations, matchers, and proof auxiliaries.
    names = ', '.join('`'+x for x in modules)
    return f'''import {top}
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[{names}]
  let mut seen : Array Name := #[]
  for (n, info) in env.constants do
    if let some idx := env.getModuleIdxFor? n then
      let origin := env.header.moduleNames[idx.toNat]!
      if wanted.contains origin && !seen.contains n then
        seen := seen.push n
        let axioms ← collectAxioms n
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .thmInfo _ => "theorem"
          | _ => "other"
        logInfo m!"FRESH|{{origin}}|{{n}}|{{kind}}|{{String.intercalate "," (axioms.toList.map toString)}}"
  logInfo m!"FRESH_TOTAL|{{seen.size}}"
'''

def parse_audit(path, modules):
    rows=[]
    for line in path.read_text().splitlines():
        if line.startswith('FRESH|'):
            _,module,name,kind,axs=line.split('|')
            rows.append({'module':module,'name':name,'kind':kind,
                         'axioms':[] if not axs else axs.split(',')})
    totals=[int(s.split('|')[1]) for s in path.read_text().splitlines() if s.startswith('FRESH_TOTAL|')]
    names=[r['name'] for r in rows]
    assert len(names)==len(set(names)), 'duplicate declaration audit'
    assert totals==[len(rows)], 'missing audit record'
    counts={m:sum(r['module']==m for r in rows) for m in modules}
    assert all(counts.values()), 'source module has no audited origin'
    forbidden=[{'name':r['name'],'module':r['module'],'axiom':a}
               for r in rows for a in r['axioms'] if a not in ALLOW]
    return {'rows':rows,'counts':counts,'total':len(rows),'forbidden':forbidden,
            'axiom_union':sorted(set(a for r in rows for a in r['axioms']))}

def prepare(arm):
    base=ROOT/'research/rmaf/algorithm/universal233'
    if arm=='source':
        cert=json.loads((base/'source_coverage/replay/20261015T075710Z/certificate.json').read_text())
        mods=list(cert['module_origin_counts'])
        pins=cert['input_hashes']
        top='Controls'
    else:
        cert=json.loads((base/'cut_realization/replay/20261015T080042Z/certificate.json').read_text())
        mods=[v['module'] for v in cert['builds']][:28]
        pins=cert['hashes']; top='CutControls'
    src={Path(p).stem:(ROOT/p,sha) for p,sha in pins.items() if p.endswith('.lean')}
    build=HERE/('isolated-'+arm); build.mkdir(exist_ok=False)
    rows=[]
    for m in mods:
        p,sha=src[m]; assert digest(p)==sha
        out=build/(m+'.lean'); out.write_bytes(p.read_bytes())
        rows.append({'module':m,'original':str(p.relative_to(ROOT)),
                     'realpath':str(p.resolve()),'sha256':sha,
                     'copy':str(out.relative_to(ROOT))})
    custom=set(mods)
    imports=[]
    for row in rows:
        p=ROOT/row['copy']
        found=re.findall(r'^import\s+([^\n]+)',p.read_text(),re.M)
        for group in found:
            for imp in group.split():
                if imp not in ('Std','Lean'):
                    assert imp in custom, (row['module'],imp,'unregistered dependency')
                imports.append({'from':row['module'],'import':imp,'registered':imp in custom})
    (build/'FreshAudit.lean').write_text(audit_text(mods,top))
    return build,mods,rows,imports

def main():
    arm=sys.argv[1]; build,mods,sources,imports=prepare(arm)
    result={'arm':arm,'sources':sources,'imports':imports,'builds':[]}
    dest=ROOT/f'research/rmaf/results/algorithm-core-completion-fresh-review-{arm}-rebuild-v1.json'
    for m in mods:
        r=run(build,m,['-o',m+'.olean']);result['builds'].append(r)
        dest.write_text(json.dumps(result,indent=2)+'\n')
        print(arm,m,r['exit'],round(r['seconds'],3),flush=True)
        if r['exit']: raise SystemExit(1)
    a=run(build,'FreshAudit'); result['builds'].append(a)
    if a['exit']:dest.write_text(json.dumps(result,indent=2)+'\n');raise SystemExit(1)
    result['audit']=parse_audit(build/'FreshAudit.log',mods)
    result['all_source_hashes_unchanged']=all(digest(ROOT/r['copy'])==r['sha256'] for r in sources)
    result['all_positive_builds_pass']=all(x['exit']==0 for x in result['builds'])
    result['olean_hashes']={m:digest(build/(m+'.olean')) for m in mods}
    dest.write_text(json.dumps(result,indent=2)+'\n')
    print('AUDIT',result['audit']['total'],result['audit']['axiom_union'],result['audit']['forbidden'],flush=True)

if __name__=='__main__': main()
