#!/usr/bin/env python3
"""One-shot exact algebra controls; no candidate/project imports or evaluator."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import platform
import sys


class Mismatch(Exception):
    def __init__(self, code, expected, observed):
        self.diagnostic = {"code": code, "expected": expected, "observed": observed}


def equal(code, expected, observed):
    if expected != observed:
        raise Mismatch(code, expected, observed)


def width(value):
    if type(value) is not int or value < 0:
        raise ValueError("natural required")
    return max(1, value.bit_length())


def clean_cases():
    cases = []

    def record(identity, expected, observed):
        equal(identity, expected, observed)
        cases.append({"id": identity, "status": "MATCH", "observed": observed})

    coeff = [4096, 512, 512, 512, 24, 272, 2048, 72, 512, 5120,
             16384, 2048, 3072, 1536, 1024, 20480, 32768, 2048,
             1024, 2048, 4096, 8192]
    a = 2
    merge = 4608*a**3 + 192*a**2 + 1
    env = 296*a**2 + 3416*a + 160
    bundle = 18*(2048*a**2) + 256
    record("C1", [108400, 37633, 3327, 8176, 16, 147712, 16128],
           [sum(coeff), merge, 5120*a**3-merge, env, 2048*a**2-env,
            bundle, 20480*a**3-bundle])

    f, c = 735030, 367508
    record("C2", [6615270, 4862469317576, 2572726],
           [9*f, 9*f*f+63*f+3*c+62, 3*f+c+128])

    x = (0+1)**3
    material = max(2**30, 2**22*x, 2**18, 2**16)
    record("C3", [1073741824, 17179869184, 0],
           [material, 16*material, 2**34*x-16*material])

    e = 48+10*19
    record("C4", [238, 244, 245, 246, 6, 2],
           [e, e+6, e+7, e+8, 252-(e+8), 32-30])

    zdeg = 4+4*32
    tdeg = zdeg+4*16
    jdeg = max(2, 32+16)
    bdeg = max(2, tdeg, jdeg, 1)
    adeg = max(6, 32+2*bdeg)
    record("C5", [132, 196, 48, 196, 424, 440],
           [zdeg, tdeg, jdeg, bdeg, adeg, adeg+16])

    # Small exact instance of the algebra only, not a candidate execution.
    q, p, source, k, u = 2, 10, 50, 3, 153
    h0, fresh, s, rpoly, d, init, gamma = 5, 2, 1, 1, 3, 7, 2
    ratio = Fraction(233, 100)
    j = h0+fresh*k*(p+1)
    z = 16*s*rpoly**4*(k+1)**4
    t = z*(p+1)**4
    b = d+t+j+10*q+4
    heap = h0+fresh*u
    scalar = 2**d+16*s*rpoly**4*(u+1)**4
    per = 16*gamma*(b+1)**2
    polynomial_a = init+k*per
    lhs = init+per*u
    rhs = polynomial_a*(source+1)
    tests = [source <= p*ratio**q, source+1 <= (p+1)*ratio**q,
             u <= k*(source+1), heap <= j*4**q,
             width(heap) <= j+2*q+1,
             scalar <= 2**d+t*4**(4*q),
             width(scalar) <= d+8*q+t+2,
             width(heap) <= b, width(scalar) <= b, lhs <= rhs]
    observed = {"source_cap": str(p*ratio**q),
                "plus_one_cap": str((p+1)*ratio**q),
                "j": j, "z": z, "t": t, "b": b, "heap": heap,
                "scalar": scalar, "widths": [width(heap), width(scalar)],
                "fee_margin": rhs-lhs, "inequalities": tests}
    expected = {"source_cap": "54289/1000", "plus_one_cap": "597179/10000",
                "j": 71, "z": 4096, "t": 59969536, "b": 59969634,
                "heap": 311, "scalar": 8999178504, "widths": [9, 34],
                "fee_margin": 350, "inequalities": [True]*10}
    record("C6", expected, observed)

    local, bound = 64*(2+1), 128*2
    record("C7", [192, 256, 64], [local, bound, bound-local])
    equal("POSITIVE_DENOMINATOR", 7, len(cases))
    return cases


def corrupted_cases():
    cases = []
    bad = [("N1", "MATERIALIZATION_MAX_TERM", 1073741824,
            max(2**22, 2**18, 2**16), 4194304),
           ("N2", "SCALAR_POWER_MULTIPLICITY", 196, (4+4*32)+3*16, 180),
           ("N3", "COUNT_PLUS_ONE", 3, 3*0, 0),
           ("N4", "LOCAL_PLUS_ONE_ABSORPTION", 192, 64*2, 128)]
    for identity, code, expected, observed, expected_bad in bad:
        try:
            equal(code, expected, observed)
        except Mismatch as error:
            equal("DIAGNOSTIC_CONTRACT", {"code": code, "expected": expected,
                                         "observed": expected_bad}, error.diagnostic)
            cases.append({"id": identity, "status": "CAUGHT", "diagnostic": error.diagnostic})
        else:
            raise Mismatch("CORRUPTION_SURVIVED", "caught", identity)
    equal("CORRUPTION_DENOMINATOR", 4, len(cases))
    return cases


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("positive", "corrupted"))
    parser.add_argument("--result", required=True, type=Path)
    args = parser.parse_args()
    if args.result.exists():
        raise FileExistsError("preserve existing evidence")
    result = {"scope": "post-argument algebra calibration only; not candidate execution",
              "mode": args.mode, "engine_qualification": "shared integer/Fraction engine, no kernel credit",
              "runtime": {"implementation": platform.python_implementation(),
                          "version": platform.python_version(), "executable": sys.executable}}
    code = 1
    try:
        result["cases"] = clean_cases() if args.mode == "positive" else corrupted_cases()
        result["status"] = "SEVEN_POSITIVES_MATCHED" if args.mode == "positive" else "FOUR_CORRUPTIONS_CAUGHT"
        code = 0 if args.mode == "positive" else 23
    except Exception as error:
        result["status"] = "UNEXPECTED_CALIBRATION_FAILURE"
        result["error"] = getattr(error, "diagnostic", {"type": type(error).__name__, "message": str(error)})
    result["exit_code"] = code
    args.result.write_text(json.dumps(result, sort_keys=True, indent=2)+"\n")
    for case in result.get("cases", []):
        print(json.dumps(case, sort_keys=True))
    print(json.dumps({key: value for key, value in result.items() if key != "cases"}, sort_keys=True))
    return code


if __name__ == "__main__":
    sys.exit(main())
