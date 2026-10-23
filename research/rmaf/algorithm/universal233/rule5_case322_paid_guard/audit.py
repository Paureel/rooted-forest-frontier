#!/usr/bin/env python3
"""Author development wrapper; fresh Std-only controls precede candidate use.
Completed detector only, no reviewer code. All stored producers are audited.
"""
from pathlib import Path
import importlib.util
D=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('completed_case322_producer_audit',D.parent/'rule5_case322/audit.py')
A=importlib.util.module_from_spec(sp);sp.loader.exec_module(A)
audit_source=A.audit_source;parse=A.parse;run_lean=A.run_lean;ALLOW=A.ALLOW;detector_controls=A.detector_controls
