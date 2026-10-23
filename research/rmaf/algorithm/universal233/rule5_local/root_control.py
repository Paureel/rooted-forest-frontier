#!/usr/bin/env python3
"""One-shot post-contact incoming/outgoing common-split actual source control.

By construction, insert the complete outside tree into one original edge of
the known bad six-label target. The bad X hull then contains the original root;
the only incident arc is outgoing and the witness must select X's root side.
"""
from pathlib import Path
import json,datetime
import local
D=Path(__file__).resolve().parent;R=D.parents[4]
out=R/'results'/('algorithm-universal233-rule5-local-root-control-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));out.mkdir()
t,u,_=local.fixture_family()['common'];bad=t[0]
def insert(T):
 if local.leaf(T):return (T,(('a','b'),'c')) if T=='ia' else T
 return tuple(insert(v) for v in T)
def mirror(T):return T if local.leaf(T) else tuple(mirror(v) for v in T[::-1])
rootT=insert(bad);C=local.classify(rootT,u)
assert C['kind']=='common' and C['witness']['target_X_side']=='root',C
M=local.classify(mirror(rootT),mirror(u))
assert M['kind']=='common' and M['witness']['target_X_side']=='root',M
incoming=local.classify(t,u);assert incoming['witness']['target_X_side']=='descendant'
record=dict(status='PASS_POSTCONTACT_ORIGINAL_ROOT_CONTROL',post_contact=True,
 target=rootT,source=u,guards=local.admitted(rootT,u),root_side=C,
 sibling_mirrored_root_side=M,incoming_side=incoming,
 meaning='Actual original split classifier fixtures; no marked optimization claim and no independent credit')
(out/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
print(record['status'],out)
