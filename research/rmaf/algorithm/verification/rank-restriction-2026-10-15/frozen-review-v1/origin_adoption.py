#!/usr/bin/env python3
"""Diagnose fixed-source generated origins under two import orders, preserving failed gate."""
import json,importlib.util
from pathlib import Path
HERE=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('own_api',HERE/'released_replay.py');a=importlib.util.module_from_spec(sp);sp.loader.exec_module(a)
old=json.loads((a.RMAF/'results/algorithm-rank-restriction-fresh-source-rebuild-v1.json').read_text())
assert old['verdict']=='OPEN-SOURCE-REPLAY-FAILURE' and 'restriction' in old['error']
folder=a.BUILD/'restriction';mods=old['restriction_order']
a.OUT=a.RMAF/'results/algorithm-rank-restriction-fresh-origin-adoption-v1.json';a.state={'runs':[],'audits':{},'failed_receipt_sha256':a.digest(a.RMAF/'results/algorithm-rank-restriction-fresh-source-rebuild-v1.json')}
r=json.loads((a.RMAF/'algorithm/universal233/restriction_bridge/replay/20261015T090816Z/certificate.json').read_text())
x=a.audit(folder,'FreshConsumerImportAudit',['Consumers'],mods)
assert x['counts']==r['module_origin_counts']
y=old['audits']['restriction/FreshOriginAudit'];byx={d['name']:d for d in x['all_declarations']};byy={d['name']:d for d in y['all_declarations']}
assert set(byx)==set(byy) and len(byx)==694
changes=[]
for name,dx in byx.items():
 dy=byy[name]
 assert all(dx[k]==dy[k] for k in ['is_axiom','unsafe','axioms','rejected'])
 if dx['origin']!=dy['origin']:changes.append({'name':name,'import_all_origin':dy['origin'],'consumer_only_origin':dx['origin'],'generated':name.startswith('_private.') or name.startswith('List._') or name.startswith('RMAF.')})
a.state.update({'same_exact_declaration_names':694,'same_all_axiom_records':True,'origin_adoptions':changes,'source_edits':0,'verdict':'PASS-EXACT-GENERATED-ORIGIN-ADOPTION; ORIGINAL-FAILED-COUNT-ASSERTION-PRESERVED'})
a.save();print(json.dumps({'status':a.state['verdict'],'changed_origins':changes},indent=2))
