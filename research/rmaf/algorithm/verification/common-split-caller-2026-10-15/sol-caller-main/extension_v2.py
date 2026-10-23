#!/usr/bin/env python3
"""Separately pinned, measured one-fixture extension; same own graph lineage."""
import json,time
from pathlib import Path
import scoped_graph_v2 as s
P=Path(__file__).resolve().parent; e=json.loads((P/'EXPECTATIONS-EXTENSION-v2.json').read_text()); at=time.perf_counter(); out=s.check_case(e['case']); v=out['costs']; profile=[v['MX']-v['X'],v['MY']-v['Y']]; assert profile==e['expected_profile']
(P/'graph-extension-v2-run1.json').write_text(json.dumps({'case':out,'profile':profile,'seconds':time.perf_counter()-at,'candidate_contact':False,'replication_credit':0,'scope':'added prerelease control; complete global family unpinned'},indent=2)+'\n'); print(json.dumps({'profile':profile,'seconds':time.perf_counter()-at}))
