"""Optional explicit run telemetry. No scientific result is inferred from logs.

Use inside a monitored script:
    from telemetry import step, metric, gate, artifact
    with step('compute', tool='nestor'): ...
    metric('completed', 12, total=20, unit='points')
    gate('independent', 'passed', detail='See the saved comparison receipt')
"""
import json
import math
import os
import time
from contextlib import contextmanager
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
STORE = Path(os.environ.get("BOOTLOOPS_MONITOR_STORE", str(ROOT / ".dashboard/runs"))).resolve()
STORE.relative_to(ROOT)
STAGES = {"input", "structure", "compute", "check", "result"}
GATES = {"known_truth", "independent", "precision", "unused"}


def emit(kind, **values):
    run_id = os.environ.get("BOOTLOOPS_MONITOR_RUN_ID")
    if not run_id:
        return False
    if not all(c.isalnum() or c == "-" for c in run_id):
        raise ValueError("Invalid run id")
    directory = STORE / run_id
    if not directory.is_dir():
        return False
    record = {"type": kind, "at": time.time(), **values}
    line = (json.dumps(record, allow_nan=False, separators=(",", ":")) + "\n").encode()
    try:
        fd = os.open(directory / "events.jsonl", os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)
        try:
            os.write(fd, line)
        finally:
            os.close(fd)
    except OSError:
        return False
    return True


@contextmanager
def step(stage, tool=None, detail=None):
    if stage not in STAGES:
        raise ValueError(f"stage must be one of {sorted(STAGES)}")
    emit("stage", stage=stage, state="running", tool=tool, detail=detail)
    try:
        yield
    except BaseException:
        emit("stage", stage=stage, state="failed", tool=tool)
        raise
    else:
        emit("stage", stage=stage, state="passed", tool=tool)


def metric(name, value, *, total=None, unit=None):
    if not isinstance(value, (int, float)) or not math.isfinite(value):
        raise ValueError("metric must be finite")
    if total is not None and (not isinstance(total, (int, float)) or not math.isfinite(total) or total <= 0):
        raise ValueError("total must be a positive finite number")
    return emit("metric", name=name, value=value, total=total, unit=unit)


def gate(name, state, *, detail=None):
    if name not in GATES or state not in {"passed", "failed", "skipped"}:
        raise ValueError("Unknown gate or state")
    return emit("gate", name=name, state=state, detail=detail, provenance="reported")


def artifact(path, *, label=None):
    resolved = Path(path).resolve()
    resolved.relative_to(ROOT)  # scope records to this workspace
    return emit("artifact", path=str(resolved.relative_to(ROOT)), label=label or resolved.name)
