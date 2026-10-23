#!/usr/bin/env python3
"""One-shot exact arithmetic audit of the retrieved baseline recurrence.

The BootLoops capability index was consulted; no installed rMAF recurrence
auditor applies. This problem-specific check is intentionally not registered
as a reusable toolkit instrument. It does not implement or verify an MAF
algorithm. Initial measured execution was under one second.

Replay: .venv/bin/python research/rmaf/baseline-recurrence-check.py
Independent Lean validation must not treat this output as an imported axiom.
"""
from fractions import Fraction
import json


def evaluate(a, b):
    c = Fraction(a, b)
    branch_sum = 2 / c + 1 / c**3 + 2 / c**4
    polynomial = c**4 - 2 * c**3 - c - 2
    numerator = a**4 - 2 * a**3 * b - a * b**3 - 2 * b**4
    assert polynomial == Fraction(numerator, b**4)
    assert branch_sum <= 1 if polynomial >= 0 else branch_sum > 1
    return {
        "base": str(c),
        "polynomial": str(polynomial),
        "branch_sum": str(branch_sum),
        "upper_bound_pass": branch_sum <= 1,
    }


rows = [evaluate(23390, 10000), evaluate(23391, 10000)]
assert not rows[0]["upper_bound_pass"], "planted false upper base was not caught"
assert rows[1]["upper_bound_pass"]
print(json.dumps({
    "recurrence": "2T(q-1)+T(q-3)+2T(q-4)",
    "characteristic_polynomial": "x^4-2*x^3-x-2",
    "evidence": "exact rational arithmetic; not Lean kernel checking",
    "rows": rows,
}, indent=2))
