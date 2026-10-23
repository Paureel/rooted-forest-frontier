"""Contract checks for recording, scoped observation, and the read-only API."""
import http.client
import json
import os
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest.mock import patch

import server
from catalog import ROOT, catalog
from server import Handler, Observer
from track import save_manifest, safe_command


class MonitorTests(unittest.TestCase):
    def setUp(self):
        base = ROOT / ".dashboard/qa"
        base.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=base)
        self.store = Path(self.temp.name) / "runs"
        self.store.mkdir()
        self.observer = Observer(self.store, discover=False)

    def tearDown(self):
        self.temp.cleanup()

    def command(self, script):
        env = dict(os.environ, BOOTLOOPS_MONITOR_STORE=str(self.store), PYTHONPATH=str(ROOT / "dashboard"))
        return [sys.executable, str(ROOT / "dashboard/track.py"), sys.executable, "-c", script], env

    def recorded(self):
        return json.loads(next(self.store.glob("*/manifest.json")).read_text())

    def test_exit_and_binary_streams_are_preserved_without_acceptance_claims(self):
        cmd, env = self.command("import sys; sys.stdout.buffer.write(b'answer\\xff\\n'); sys.stderr.write('diagnostic\\n'); sys.exit(7)")
        p = subprocess.run(cmd, env=env, capture_output=True)
        self.assertEqual(p.returncode, 7)
        self.assertEqual(p.stdout, b"answer\xff\n")
        self.assertEqual(p.stderr, b"diagnostic\n")
        detail = self.observer.detail(self.observer.manifests()[0])
        self.assertEqual(detail["status"], "failed")
        self.assertEqual(detail["exit_code"], 7)
        self.assertEqual(detail["gates"], {})
        self.assertEqual(detail["stages"], {})

    def test_live_samples_and_persistent_completion(self):
        cmd, env = self.command("import time; print('working',flush=True); time.sleep(1.2); print('done')")
        p = subprocess.Popen(cmd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        deadline = time.monotonic()+3
        while time.monotonic()<deadline:
            runs = self.observer.manifests()
            if runs and runs[0].get("pid"): break
            time.sleep(.02)
        run = runs[0]
        self.assertEqual(run["status"], "running")
        self.observer.sample(run)
        time.sleep(.05)
        self.observer.sample(run)
        detail = self.observer.detail(run)
        self.assertGreater(detail["resources"][-1]["memory_mb"], 0)
        self.assertIsNotNone(detail["resources"][-1]["cpu"])
        out, err = p.communicate(timeout=4)
        self.assertEqual(p.returncode,0)
        self.assertEqual(out,b"working\ndone\n")
        self.assertEqual(err,b"")
        restarted = Observer(self.store, discover=False)
        completed = restarted.detail(restarted.manifests()[0])
        self.assertEqual(completed["status"],"completed")
        self.assertEqual(completed["gates"],{})

    def test_semantic_telemetry_survives_long_output(self):
        cmd, env = self.command("from telemetry import step,metric,gate;\nwith step('compute',tool='nestor'): metric('completed',3,total=5,unit='points')\ngate('independent','passed',detail='test receipt')\nfor i in range(750): print('line',i)")
        p = subprocess.run(cmd,env=env,capture_output=True)
        self.assertEqual(p.returncode,0,p.stderr)
        detail = self.observer.detail(self.observer.manifests()[0])
        self.assertEqual(detail["gates"]["independent"]["state"],"passed")
        self.assertEqual(detail["metrics"]["completed"]["value"],3)
        self.assertEqual(detail["metrics"]["completed"]["total"],5)
        self.assertEqual(detail["stages"]["compute"]["state"],"passed")
        self.assertIn("nestor",detail["tools"])
        self.assertLessEqual(len(detail["events"]),100)
        restarted = Observer(self.store,discover=False)
        self.assertEqual(restarted.detail(restarted.manifests()[0])["gates"]["independent"]["state"],"passed")

    def test_partial_event_is_retried_and_pid_reuse_does_not_sample(self):
        d=self.store/"fixture";d.mkdir()
        manifest={"id":"fixture","title":"Fixture","started":time.time(),"status":"running","pid":os.getpid(),"process_created":0,"source":"recorded"}
        save_manifest(d,manifest)
        (d/"events.jsonl").write_bytes(b'{"type":"gate","at":1,"name":"independent",')
        run=self.observer.manifests()[0]
        self.assertEqual(self.observer.detail(run)["gates"],{})
        with (d/"events.jsonl").open("ab") as f:f.write(b'"state":"passed"}\n')
        self.assertEqual(self.observer.detail(run)["gates"]["independent"]["state"],"passed")
        self.observer.sample(run)
        self.assertEqual(self.observer.detail(run)["resources"],[])

    def test_unrelated_plugin_with_inherited_cwd_is_excluded(self):
        class Fake:
            info={"pid":987654,"name":"python","cmdline":["/outside/python","-m","valheim_codex","stdio"],"cwd":str(ROOT),"create_time":time.time(),"ppid":0}
        with patch('server.psutil.process_iter',return_value=[Fake()]):self.observer.discover_runs([])
        self.assertEqual(self.observer.manifests(),[])

    def test_command_credentials_redacted(self):
        self.assertEqual(safe_command(['python','x.py','--token','private','--api-key=secret']),['python','x.py','--token','[redacted]','--api-key=[redacted]'])

    def test_peak_covers_the_whole_run_not_only_chart_window(self):
        directory=self.store/'peak-fixture';directory.mkdir()
        save_manifest(directory,{'id':'peak-fixture','title':'Peak fixture','started':1,'ended':400,'status':'completed','source':'recorded'})
        with (directory/'events.jsonl').open('w') as file:
            for i in range(350):
                file.write(json.dumps({'type':'resource','at':i+1,'cpu':300 if i==0 else 2,'memory_mb':500 if i==0 else 20})+'\n')
        detail=self.observer.detail(self.observer.manifests()[0])
        self.assertEqual(len(detail['resources']),240)
        self.assertEqual(detail['peak'],{'cpu':300,'memory_mb':500})
        self.assertEqual(max(r['cpu'] for r in detail['resources']),2)

    def test_catalog_coverage_and_imported_scopes(self):
        c=catalog();self.assertEqual(len(c['tools']),50);self.assertEqual(len(c['protocols']),12)
        imported=self.observer.imported()
        self.assertEqual(imported['gates'],{})
        self.assertEqual(sum(v=='passed' for v in imported['packages'].values()),45)
        self.assertEqual(sum(v=='failed' for v in imported['packages'].values()),2)

    def test_api_is_read_only_local_and_path_scoped(self):
        server.OBSERVER=self.observer
        httpd=server.ThreadingHTTPServer(('127.0.0.1',0),Handler)
        thread=threading.Thread(target=httpd.serve_forever,daemon=True);thread.start()
        def request(path,method='GET',headers=None):
            conn=http.client.HTTPConnection('127.0.0.1',httpd.server_port,timeout=3)
            conn.request(method,path,headers=headers or {})
            response=conn.getresponse();status=response.status;data=response.read();conn.close();return status,data
        try:
            status,data=request('/api/state');self.assertEqual(status,200)
            self.assertEqual(json.loads(data)['scope'],'workspace')
            self.assertEqual(request('/api/state',headers={'Origin':'https://outside.example'})[0],403)
            self.assertEqual(request('/api/state',headers={'Host':'outside.example'})[0],403)
            self.assertEqual(request('/%2e%2e/server.py')[0],404)
            self.assertEqual(request('/api/guide/../../activate.sh')[0],404)
            self.assertEqual(request('/api/guide/nestor')[0],200)
            self.assertEqual(request('/api/state',method='POST')[0],501)
        finally:
            httpd.shutdown();httpd.server_close();thread.join(timeout=2)


if __name__=='__main__':unittest.main()
