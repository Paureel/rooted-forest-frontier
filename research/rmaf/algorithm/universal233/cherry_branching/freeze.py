#!/usr/bin/env python3
"""Freeze the completed local AUTHOR proof and exact source-bound receipts."""
from pathlib import Path
import datetime,hashlib,json,sys
D=Path(__file__).resolve().parent;R=D.parents[4];M=D/'CHERRY-BRANCH-MANIFEST-v1.json'
assert not M.exists(),'EXISTING_IMMUTABLE_MANIFEST'
O=Path(sys.argv[1]).resolve();assert O.parent==R/'results' and O.name.startswith('algorithm-universal233-cherry-branch-')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
c=json.loads((O/'certificate.json').read_text());assert c['status']=='PASS_AUTHOR_KERNEL'
for e in c['source_entries']:assert sha(R/e['path'])==e['sha256']
for p,h in c['input_hashes'].items():assert sha(R/p)==h
pre=R/c['preproof']['receipt'];assert sha(pre/'certificate.json')==c['preproof']['sha256']
paths=[p for p in D.iterdir() if p.is_file()]
paths += [p for p in O.iterdir() if p.is_file()]+[p for p in pre.iterdir() if p.is_file()]
rows=[dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=p.stat().st_size) for p in sorted(set(paths))]
m=dict(version=1,frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='FROZEN AUTHOR KERNEL; fresh hostile/nonauthor verification pending',no_further_writes=True,all_three_main_milestones='OPEN',full_solver=False,full_runtime=False,novelty_claim=False,fresh_nonauthor_acceptance=False,canonical_receipt=str((O/'certificate.json').relative_to(R)),source_builds=c['source_builds'],module_origin_declarations=c['module_origin_declarations'],standard_axioms_observed=c['axiom_union'],completed='actual ordinary t1 no-larger original agreement exchange, deterministic and two-child consumers; arbitrary pendant residual graph/partition and t>=3 branch cover; literal original cuts, states, paid budgets, priority selector; conditional exact child solver interface',first_remaining_mathematical_consumer='Complete recursive exact solver satisfying the explicit child-specific ExactBoundedChild IH; separate hard2/special-priority/global termination/reconstruction and runtime assembly',source_work='SOURCE-WORK.md; qualified mathematical source-inspection argument',independence='All proof sources/control values are author development contacts; fresh nonauthor acceptance pending',excluded_mutable_development=['build/'],immutable_files=rows)
M.write_text(json.dumps(m,indent=2)+'\n')
for p in set(paths):p.chmod(0o444)
M.chmod(0o444)
print('FROZEN',len(rows),'files;',c['source_builds'],'modules;',c['module_origin_declarations'],'module-origin declarations')
print(M)
