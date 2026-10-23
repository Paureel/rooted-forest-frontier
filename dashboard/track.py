#!/usr/bin/env python3
"""Transparent local recorder for workspace launchers; preserves exit codes.

It records actual process/output events. It never interprets process activity
as scientific verification. Interactive Python retains its original terminal.
"""
import json
import os
import re
import signal
import subprocess
import sys
import threading
import time
import uuid
from pathlib import Path

import psutil
from catalog import EXPLAIN, ROOT
from telemetry import STORE, emit


def save_manifest(directory, data):
    tmp = directory / "manifest.tmp"
    tmp.write_text(json.dumps(data, indent=2))
    os.replace(tmp, directory / "manifest.json")


def tool_for(command):
    joined = " ".join(command)
    for name in sorted(EXPLAIN, key=len, reverse=True):
        if f"tools/{name}/" in joined or re.search(r"(?:^|\s)(?:-m\s+)?" + re.escape(name.replace("-", "_")) + r"(?:\.|\s|$)", joined):
            return name
    return None


def safe_command(command):
    result, hide = [], False
    for arg in command:
        if hide:
            result.append("[redacted]"); hide = False
        elif re.match(r"--?(token|api[-_]key|password|secret)(?:=|$)", arg, re.I):
            if "=" in arg:
                result.append(arg.split("=", 1)[0] + "=[redacted]")
            else:
                result.append(arg); hide = True
        else:
            result.append(arg)
    return result


def run(command):
    if not command:
        return 2
    # Preserve REPL and explicit interactive terminal semantics.
    if len(command) == 1 or "-i" in command:
        os.execvpe(command[0], command, os.environ)
    run_id = str(uuid.uuid4())
    directory = STORE / run_id
    try:
        STORE.mkdir(parents=True, exist_ok=True)
        directory.mkdir(mode=0o700)
    except OSError:
        print("BootLoops: recorder unavailable; running without telemetry.", file=sys.stderr)
        os.execvpe(command[0], command, os.environ)
    tool = tool_for(command)
    program = Path(command[0]).name.lower()
    engine = 'Lean' if program in {'lean', 'lake'} else 'Julia' if 'julia' in program else 'Python'
    title = EXPLAIN[tool][0] if tool else ("Toolkit check" if any("run_selftests.py" in s for s in command) else next((Path(s).stem for s in command[1:] if s.endswith((".py", ".lean", ".jl"))), engine + ' run'))
    title = os.environ.get("BOOTLOOPS_RUN_TITLE", title)
    now = time.time()
    manifest = {"id": run_id, "title": title, "started": now, "ended": None, "status": "running",
                "command": safe_command(command), "cwd": str(Path.cwd()), "tool": tool, "engine": engine, "source": "recorded", "pid": None}
    save_manifest(directory, manifest)
    env = dict(os.environ, BOOTLOOPS_MONITOR_RUN_ID=run_id, PYTHONUNBUFFERED="1")
    os.environ["BOOTLOOPS_MONITOR_RUN_ID"] = run_id
    emit("run_started", title=title)
    try:
        child = subprocess.Popen(command, env=env, stdin=None, stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        manifest.update(pid=child.pid, process_created=psutil.Process(child.pid).create_time())
        save_manifest(directory, manifest)
        emit("process_started", tool=tool, pid=child.pid)
    except BaseException as exc:
        manifest.update(status="failed", ended=time.time(), exit_code=127)
        save_manifest(directory, manifest)
        emit("error", text=str(exc))
        raise

    def forward(signum, _frame):
        try:
            os.killpg(child.pid, signum)
        except ProcessLookupError:
            pass

    for sig in (signal.SIGINT, signal.SIGTERM):
        signal.signal(sig, forward)

    def relay(pipe, target, stream):
        pending = b""
        while True:
            chunk = os.read(pipe.fileno(), 4096)
            if not chunk:
                break
            try:
                target.buffer.write(chunk); target.buffer.flush()
            except (BrokenPipeError, OSError):
                pass
            pending += chunk
            while b"\n" in pending:
                line, pending = pending.split(b"\n", 1)
                text = line.decode("utf-8", "replace")
                emit("output", stream=stream, text=text[-4000:])
                match = re.match(r"\s*(PASS|FAIL|REFUSED \(by design\))\s+\[\s*[^\]]+\]\s+(\S+)", text)
                if match and match[2] in EXPLAIN:
                    emit("package_result", tool=match[2], state={"PASS": "passed", "FAIL": "failed", "REFUSED (by design)": "needs_data"}[match[1]], scope="package_battery")
            if len(pending) > 16000:
                emit("output", stream=stream, text=pending[-4000:].decode("utf-8", "replace")); pending = b""
        if pending:
            emit("output", stream=stream, text=pending[-4000:].decode("utf-8", "replace"))

    threads = [threading.Thread(target=relay, args=(child.stdout, sys.stdout, "stdout")), threading.Thread(target=relay, args=(child.stderr, sys.stderr, "stderr"))]
    for thread in threads:
        thread.start()
    code = child.wait()
    for thread in threads:
        thread.join()
    manifest.update(status="completed" if code == 0 else ("interrupted" if code < 0 else "failed"), ended=time.time(), exit_code=code)
    emit("run_finished", exit_code=code, state=manifest["status"])
    save_manifest(directory, manifest)
    return code if code >= 0 else 128 - code


if __name__ == "__main__":
    raise SystemExit(run(sys.argv[1:]))
