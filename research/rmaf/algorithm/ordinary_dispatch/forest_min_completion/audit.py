#!/usr/bin/env python3
"""One-shot author wrapper around completed stored-producer detector."""
from pathlib import Path
import importlib.util
D=Path(__file__).resolve().parent;R=D.parents[4]
p=R/'research/rmaf/algorithm/universal233/rule5_case322/audit.py'
sp=importlib.util.spec_from_file_location('completed_author_producer_detector',p)
A=importlib.util.module_from_spec(sp);sp.loader.exec_module(A)
audit_source=A.audit_source;parse=A.parse;run_lean=A.run_lean;ALLOW=A.ALLOW;detector_controls=A.detector_controls
