#!/usr/bin/env python3
from pathlib import Path
import json,importlib.util
H=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('own_api',H/'released_replay.py');a=importlib.util.module_from_spec(s);s.loader.exec_module(a)
oldpath=a.RMAF/'results/algorithm-rank-restriction-fresh-joint-consumer-v1.json';old=json.loads(oldpath.read_text());assert old['verdict']=='OPEN-JOINT-SEAM-FAILURE' and old['runs'][-1]['module']=='ConsumerInterface'
assert all(x['returncode']==0 for x in old['runs'][:-1])
a.OUT=a.RMAF/'results/algorithm-rank-restriction-fresh-joint-consumer-v2.json';a.state={'runs':[],'audits':{},'source_build_receipt_sha256':a.digest(oldpath),'adapters':old['adapters'],'failed_attempt_retained':True,'scope':'Guarded theorem seam only; actual live solver/classifier unreviewed and all main milestones OPEN'}
f=a.BUILD/'joint';p=H/'ConsumerInterfaceV2.lean';(f/p.name).write_bytes(p.read_bytes());mods=old['order'][:-1]+['ConsumerInterfaceV2']
try:
 a.compile_one(f,'ConsumerInterfaceV2');x=a.audit(f,'FreshJointOriginAuditV2',mods,mods)
 assert not x['bad'];a.state['verdict']='PASS-GUARDED-ACTUAL-OUTPUT-FORWARD-REVERSE-AND-EXACT-COST-SEAM';a.state['modules']=mods;a.state['all_three_main_milestones']='OPEN';a.save();print(json.dumps({'verdict':a.state['verdict'],'origins':len(mods),'declarations':x['total']}))
except Exception as e:a.state['verdict']='OPEN-JOINT-SEAM-V2-FAILURE';a.state['error']=repr(e);a.save();raise
