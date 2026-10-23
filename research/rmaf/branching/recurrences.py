#!/usr/bin/env python3
"""Exact recurrence arithmetic certificates, not structural rMAF proofs."""
from fractions import Fraction
from pathlib import Path
import json


def mass(c, vector):
    return sum((c ** (-d) for d in vector), Fraction())


def root_bracket(vector, denominator=10**9):
    low, high = denominator, 4 * denominator
    while high-low > 1:
        middle=(low+high)//2
        if mass(Fraction(middle,denominator),vector)>1:
            low=middle
        else:
            high=middle
    return {'lower':str(Fraction(low,denominator)),
            'upper':str(Fraction(high,denominator)),
            'lower_mass_gt_1':mass(Fraction(low,denominator),vector)>1,
            'upper_mass_le_1':mass(Fraction(high,denominator),vector)<=1}


def main():
    c=Fraction(231,100)
    vectors={
        'published_bottleneck':[1,1,3,4,4],
        'conditional_macro_a':[1,1,4,4,4],
        'conditional_macro_b':[1,1,3,5,5],
        'conditional_macro_c':[1,1,3,4],
        'whidden_t3':[1,1,3],
        'lemma13_worst':[1,2,2,2],
        'lemma13_five_two_cuts':[2,2,2,2,2],
        'split':[1,1],
        'disjoint_t1':[2,2],
    }
    assert mass(Fraction(2),[1,1])==1 # Known exact branching base.
    assert mass(Fraction(1),[1,1])>1 # Corrupted base caught.
    entries={name:{'vector':v,'mass_at_231_100':str(mass(c,v)),
                   'certificate':mass(c,v)<=1,'exact_root_bracket':root_bracket(v)}
             for name,v in vectors.items()}
    assert not entries['published_bottleneck']['certificate']
    assert all(entry['certificate'] for name,entry in entries.items()
               if name!='published_bottleneck')
    result={'target_base':str(c),'controls_passed':2,
            'structural_hypothesis_proved':False,'recurrences':entries,
            'scope':'Exact arithmetic only. The improved macro cover is an open lemma.'}
    output=Path(__file__).parents[1]/'results'/'branching-recurrences.json'
    output.write_text(json.dumps(result,indent=2)+'\n')
    print('target',c)
    for name,entry in entries.items():
        print(name,entry['mass_at_231_100'],entry['certificate'])


if __name__=='__main__':
    main()
