#!/usr/bin/env python3
"""One-shot total finite paid-cover solver entry point; no faster bound claimed.

Input JSON: target, source list (or source_tree), optional budget.
With budget, decide/refine that state. Without budget, test 0..n-m cuts
and return the first feasible witness. Empty convention is zero components.
"""
import argparse
import json
from pathlib import Path
from cover_solver import parse_state
from full_cover import solve_full


def execute(raw):
    target = raw['target']
    sources = raw['source'] if 'source' in raw else [raw['source_tree']]
    parsed, forest = parse_state(target,sources,0)
    if 'budget' in raw:
        result = solve_full(target,sources,raw['budget'])
        result['tested_budgets'] = [raw['budget']]
    else:
        maximum = 0 if parsed is None else len(parsed.labels)-len(forest)
        result = None
        for q in range(maximum+1):
            trial = solve_full(target,sources,q)
            if trial['feasible']:
                result = trial
                result['tested_budgets'] = list(range(q+1))
                break
        if result is None:
            raise AssertionError('singleton upper bound failed')
    if result['feasible']:
        result['components'] = len(result['partition'])
    result['initial_source_components'] = len(forest)
    result['claim_status'] = 'finite enumerative candidate; full proof and improved exponent OPEN'
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('input',type=Path)
    a = p.parse_args()
    print(json.dumps(execute(json.loads(a.input.read_text())),indent=2))
