#!/usr/bin/env python3
"""One-shot author wrapper around the immutable completed producer detector.
No reviewer instrument is imported. Std-only fixtures are rebuilt in the new
isolated results directory before candidate producers.
"""
from pathlib import Path
import importlib.util
D=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('completed_case322_audit',D.parent/'rule5_case322/audit.py')
A=importlib.util.module_from_spec(sp);sp.loader.exec_module(A)
audit_source=A.audit_source;parse=A.parse;run_lean=A.run_lean;ALLOW=A.ALLOW;detector_controls=A.detector_controls
