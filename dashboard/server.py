#!/usr/bin/env python3
"""Workspace-only, read-only dashboard server. No launch/stop HTTP endpoints."""
import argparse
import json
import mimetypes
import os
import signal
import threading
import time
import uuid
from collections import Counter, deque
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, unquote, urlparse

import psutil
from catalog import ROOT, catalog
from telemetry import STORE
from track import safe_command, save_manifest, tool_for
from proof import ProofObserver

DIST = Path(__file__).resolve().parent / "dist"
CATALOG = catalog()
TOOL_IDS = {t["id"] for t in CATALOG["tools"]}
STOP = threading.Event()


def append(directory, event):
    line = (json.dumps({"at": time.time(), **event}, allow_nan=False) + "\n").encode()
    fd = os.open(directory / "events.jsonl", os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)
    try:
        os.write(fd, line)
    finally:
        os.close(fd)


class Observer:
    def __init__(self, store=STORE, discover=True):
        self.store = store
        self.discover = discover
        self.lock = threading.RLock()
        self.processes = {}
        self.run_cache = {}
        self.cache = {}
        self.proof = ProofObserver(history=(self.store.parent / 'proof-history.jsonl') if self.store != STORE else None)
        self.store.mkdir(parents=True, exist_ok=True)

    def manifests(self):
        runs = []
        for path in self.store.glob("*/manifest.json"):
            try:
                item = json.loads(path.read_text())
                item["directory"] = str(path.parent)
                runs.append(item)
            except (OSError, ValueError):
                continue
        return sorted(runs, key=lambda r: r["started"], reverse=True)

    def sample(self, item):
        pid = item.get("pid")
        if not pid:
            return
        try:
            process = psutil.Process(pid)
            if abs(process.create_time() - item.get("process_created", 0)) > .01:
                raise psutil.NoSuchProcess(pid)
            if process.status() == psutil.STATUS_ZOMBIE:
                raise psutil.NoSuchProcess(pid)
            children = [process] + process.children(recursive=True)
        except psutil.NoSuchProcess:
            # A launcher owns its exit code. Give it time to write the final record.
            last = self.run_cache.setdefault(item["id"], {"missing_since": time.time()})
            if time.time() - last.get("missing_since", time.time()) > 4:
                item = {k: v for k, v in item.items() if k != "directory"}
                item.update(status="ended" if item.get("source") == "observed" else "interrupted", ended=time.time())
                save_manifest(self.store / item["id"], item)
            return
        except (psutil.AccessDenied, psutil.Error):
            return
        self.run_cache.pop(item["id"], None)
        cpu, rss, seen, primed = 0., 0, 0, True
        for child in children:
            try:
                key = (child.pid, child.create_time())
                cached = self.processes.get(key)
                if cached is None:
                    cached = self.processes[key] = child
                    cached.cpu_percent(); primed = False
                else:
                    cpu += cached.cpu_percent()
                rss += cached.memory_info().rss
                seen += 1
            except (psutil.Error, OSError):
                continue
        append(Path(item["directory"]), {"type": "resource", "cpu": round(cpu, 2) if primed and seen else None,
                                          "memory_mb": round(rss / 1024**2, 2) if seen else None,
                                          "processes": seen, "partial": seen < len(children)})

    def discover_runs(self, runs):
        known = {r.get("pid") for r in runs if r["status"] == "running"}
        descendants = set(known)
        for pid in known - {None}:
            try:
                descendants.update(p.pid for p in psutil.Process(pid).children(recursive=True))
            except psutil.Error:
                pass
        candidates = []
        for proc in psutil.process_iter(["pid", "name", "cmdline", "cwd", "create_time", "ppid"]):
            try:
                info = proc.info
                if info["pid"] in descendants or info["pid"] == os.getpid():
                    continue
                if not any(s in (info["name"] or "").lower() for s in ("python", "julia")):
                    continue
                cwd = Path(info["cwd"] or "/").resolve()
                if not cwd.is_relative_to(ROOT):
                    continue
                cmd = info["cmdline"] or []
                if any("/dashboard/" in s or "dashboard/server.py" in s or "dashboard/track.py" in s or "unittest" == s for s in cmd):
                    continue
                script_here = any(s.endswith((".py", ".jl")) and (cwd / s).resolve().is_relative_to(ROOT) and (cwd / s).is_file() for s in cmd[1:])
                if not script_here and not tool_for(cmd) and not any(str(ROOT / "bootloops") in s or "bootloops/tools/" in s for s in cmd):
                    continue
                # An observer is workspace-scoped. No outside process is registered,
                # even if its command happens to mention BootLoops.
                candidates.append((proc, info, cmd, cwd))
            except (psutil.Error, OSError):
                continue
        ids = {i[1]["pid"] for i in candidates}
        for proc, info, cmd, cwd in candidates:
            if info["ppid"] in ids or info["ppid"] in descendants:
                continue
            name = tool_for(cmd)
            run_id = str(uuid.uuid4())
            directory = self.store / run_id
            directory.mkdir(mode=0o700)
            title = next((t["name"] for t in CATALOG["tools"] if t["id"] == name), "Workspace process")
            item = {"id": run_id, "title": title, "started": info["create_time"],
                    "ended": None, "status": "running", "source": "observed", "pid": info["pid"],
                    "process_created": info["create_time"], "cwd": str(cwd), "command": safe_command(cmd), "tool": name}
            save_manifest(directory, item)
            append(directory, {"type": "process_started", "tool": name, "pid": info["pid"], "observed": True})

    def collect(self):
        while not STOP.wait(1):
            with self.lock:
                runs = self.manifests()
                if self.discover:
                    self.discover_runs(runs)
                for item in self.manifests():
                    if item["status"] == "running":
                        self.sample(item)
                # Process objects are only retained for live processes.
                live = set()
                for key, process in self.processes.items():
                    try:
                        if process.is_running(): live.add(key)
                    except psutil.Error: pass
                self.processes = {k: v for k, v in self.processes.items() if k in live}

    def events(self, run):
        path = Path(run["directory"]) / "events.jsonl"
        def empty_cache():
            return {"offset": 0, "events": deque(maxlen=600), "resources": deque(maxlen=240),
                    "stages": {}, "gates": {}, "metrics": {}, "tools": set(), "packages": {}, "artifacts": deque(maxlen=20), "peak": {"cpu": None, "memory_mb": None}}
        cached = self.cache.setdefault(run["id"], empty_cache())
        if path.is_file():
            with path.open("rb") as fh:
                if path.stat().st_size < cached["offset"]:
                    cached.clear(); cached.update(empty_cache())
                fh.seek(cached["offset"])
                while True:
                    line = fh.readline()
                    if not line or not line.endswith(b"\n"):
                        break
                    cached["offset"] = fh.tell()
                    try:
                        event = json.loads(line)
                        if not isinstance(event, dict) or not isinstance(event.get("type"), str): continue
                        if event["type"] == "resource": cached["resources"].append(event)
                        else: cached["events"].append(event)
                        kind = event["type"]
                        if kind == "resource":
                            for field in ("cpu", "memory_mb"):
                                if isinstance(event.get(field), (float, int)):
                                    cached["peak"][field] = max(event[field], cached["peak"][field] or 0)
                        if event.get("tool") in TOOL_IDS: cached["tools"].add(event["tool"])
                        if kind == "stage": cached["stages"][event["stage"]] = event
                        elif kind == "gate": cached["gates"][event["name"]] = event
                        elif kind == "metric": cached["metrics"][event["name"]] = event
                        elif kind == "package_result": cached["packages"][event["tool"]] = event["state"]
                        elif kind == "artifact": cached["artifacts"].append(event)
                    except (ValueError, KeyError, TypeError): pass
        return list(cached["events"]), list(cached["resources"])

    def detail(self, run):
        events, resources = self.events(run)
        summary = self.cache[run["id"]]
        stages, gates, metrics, tools, packages, artifacts = summary["stages"], summary["gates"], summary["metrics"], set(summary["tools"]), summary["packages"], list(summary["artifacts"])
        if run.get("tool"): tools.add(run["tool"])
        return {**{k: v for k, v in run.items() if k != "directory"}, "events": events[-100:], "resources": resources,
                "stages": stages, "gates": gates, "metrics": metrics, "tools": sorted(tools), "packages": packages,
                "artifacts": artifacts[-20:], "peak": summary["peak"]}

    def imported(self):
        path = ROOT / "installation-validation.json"
        data = json.loads(path.read_text())
        packages = data["packages"]
        return {"id": "installation", "title": "Installation check", "started": path.stat().st_mtime,
                "ended": path.stat().st_mtime, "status": "partial", "source": "imported", "date": data["date"],
                "tools": list(packages), "stages": {}, "gates": {}, "metrics": {}, "resources": [], "events": [],
                "packages": {k: {"PASS": "passed", "FAIL": "failed", "REFUSED (by design)": "needs_data"}[v["status"]] for k, v in packages.items()},
                "checks": [{"tool": k, "seconds": v.get("wall_s", v.get("secs")), "state": v["status"], "tail": v.get("tried", [{}])[-1].get("tail", "")} for k, v in packages.items()],
                "note": "Combined package batteries from three installation runs. Package checks are not acceptance of a new scientific result.",
                "records": data["run_records"], "artifacts": []}

    def snapshot(self, selected=None):
        with self.lock:
            runs = self.manifests()
            history = [{k: v for k, v in r.items() if k in {"id", "title", "started", "ended", "status", "source", "tool", "engine", "exit_code"}} for r in runs]
            imported = self.imported()
            history.append({k: imported[k] for k in ("id", "title", "started", "ended", "status", "source")})
            live = [r for r in runs if r["status"] == "running"]
            chosen = next((r for r in runs if r["id"] == selected), live[0] if live and not selected else None)
            detail = imported if selected == "installation" else (self.detail(chosen) if chosen else None)
            return {"at": time.time(), "active": [r["id"] for r in live], "history": history[:100], "selected": detail,
                    "scope": "workspace", "workspace": ROOT.name, "proof": self.proof.snapshot()}


OBSERVER = None


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *_):
        pass

    def response(self, status, content, content_type="application/json; charset=utf-8"):
        if isinstance(content, (dict, list)): content = json.dumps(content, allow_nan=False).encode()
        if isinstance(content, str): content = content.encode()
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(content)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Content-Security-Policy", "default-src 'self'; script-src 'self'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; connect-src 'self'; font-src 'self'; base-uri 'none'; frame-ancestors 'none'")
        self.end_headers()
        self.wfile.write(content)

    def do_GET(self):
        origin = self.headers.get("Origin")
        host = self.headers.get("Host", "").split(":")[0]
        if host not in {"localhost", "127.0.0.1"} or (origin and urlparse(origin).netloc != self.headers.get("Host")):
            return self.response(403, {"error": "Local requests only"})
        url = urlparse(self.path)
        selected = parse_qs(url.query).get("run", [None])[0]
        if url.path == "/api/catalog": return self.response(200, CATALOG)
        if url.path == "/api/state": return self.response(200, OBSERVER.snapshot(selected))
        if url.path == "/api/proof":
            with OBSERVER.lock:
                return self.response(200, OBSERVER.proof.snapshot())
        if url.path == "/api/proof/file":
            try:
                return self.response(200, OBSERVER.proof.read_file(parse_qs(url.query).get('path', [''])[0]))
            except (OSError, ValueError, UnicodeError) as exc:
                return self.response(404, {'error': str(exc)})
        if url.path == "/api/events":
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Connection", "close")
            self.end_headers()
            try:
                while not STOP.is_set():
                    data = json.dumps(OBSERVER.snapshot(selected), allow_nan=False, separators=(",", ":"))
                    self.wfile.write(("data: " + data + "\n\n").encode()); self.wfile.flush()
                    if STOP.wait(1): break
            except (BrokenPipeError, ConnectionResetError, OSError): pass
            self.close_connection = True
            return
        if url.path.startswith("/api/guide/"):
            name = unquote(url.path.removeprefix("/api/guide/"))
            entries = CATALOG["tools"] + CATALOG["protocols"]
            entry = next((e for e in entries if e["id"] == name), None)
            if entry is None: return self.response(404, {"error": "Unknown tool"})
            path = (ROOT / entry["guide"]).resolve()
            if not path.is_relative_to(ROOT): return self.response(403, {"error": "Outside workspace"})
            return self.response(200, {"path": entry["guide"], "text": path.read_text()})
        path = (DIST / unquote(url.path).lstrip("/")).resolve() if url.path != "/" else DIST / "index.html"
        if not path.is_relative_to(DIST) or not path.is_file(): return self.response(404, {"error": "Not found"})
        return self.response(200, path.read_bytes(), mimetypes.guess_type(path)[0] or "application/octet-stream")


def main():
    global OBSERVER
    parser = argparse.ArgumentParser()
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--no-discovery", action="store_true")
    args = parser.parse_args()
    OBSERVER = Observer(discover=not args.no_discovery)
    threading.Thread(target=OBSERVER.collect, daemon=True).start()
    server = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    server.daemon_threads = True
    print(f"BootLoops dashboard: http://127.0.0.1:{args.port}", flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        STOP.set(); server.server_close()


if __name__ == "__main__": main()
