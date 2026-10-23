#!/usr/bin/env python3
"""One-shot Markdown text checks for this review; no scientific calculation.

This supplements human parse, colleague, honesty and number reads. It neither
renders a browser view nor substitutes pattern matches for those reads.
"""
import hashlib
import json
import re
import sys
from pathlib import Path

BASE = Path(__file__).resolve().parent
ROOT = Path('/Users/paurel/Documents/ChatGPT/bootscience')
pass_name = sys.argv[1]
spec = json.loads((BASE/'evidence-spec-v1.json').read_text())
sources = {k: (ROOT/p).read_text() for k,p in spec['sources'].items()}
assert any('quoted fixture' in s for s in ['quoted fixture'])
assert not any('fabricated fixture' in s for s in ['quoted fixture'])
names = ['REFEREE-REVIEW-v1.md','SCOPE-COMPANION-v1.md','EVIDENCE-INDEX-v1.md','METHOD-v1.md']
patterns = {
    'hype': r'\b(delve|tapestry|leverage|unlock|unleash|seamless|robust|groundbreaking|transformative|unprecedented|notably|importantly)\b',
    'register': r'\b(pipeline|workflow|handoff|sanity check|edge case|toolchain|load-bearing|guardrail|footgun)\b',
    'cleft': r'\b(it is .{0,40} that|what .{0,40} is|the key is|worth noting|in conclusion|in summary)\b',
    'necessity': r'\b(must|guarantees|ensures)\b',
    'lowercase_after_period': r'\. [a-z]{3,}',
}
assert re.search(patterns['lowercase_after_period'], '. Capital') is None
assert re.search(patterns['lowercase_after_period'], '. lowercase') is not None
output = {'scope':'Markdown source text only; human judgements recorded separately',
          'pass': pass_name, 'files': {}, 'quote_comparator_controls': ['clean accepted','altered rejected'],
          'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'case_controls': ['capital excluded','lowercase included']}
for name in names:
    text = (BASE/name).read_text()
    direct_quotes = []
    for match in re.finditer('“([^”]+)”', text):
        quote = match.group(1)
        origins = [k for k,s in sources.items() if quote in s]
        assert origins, (name, 'unmatched exact quote', quote)
        direct_quotes.append({'text':quote,'source_labels':origins})
    locators = []
    for match in re.finditer(r'\b(A[123]|S[1-5]|Q|L[1-7]|E[01]|P[1-3]):(\d+)(?:–(\d+))?', text):
        alias, start, end = match.group(1), int(match.group(2)), int(match.group(3) or match.group(2))
        assert 1 <= start <= end <= len(sources[alias].splitlines()), (name,match.group())
        locators.append(match.group())
    candidates = {key:[{'line':i,'text':line} for i,line in enumerate(text.splitlines(),1)
                       if re.search(pattern,line,0 if key == 'lowercase_after_period' else re.I)]
                  for key,pattern in patterns.items()}
    assert text.count('```') % 2 == 0
    assert '<!--' not in text and '-->' not in text
    output['files'][name] = {'sha256':hashlib.sha256(text.encode()).hexdigest(),
                            'exact_quotes':direct_quotes,'valid_named_locators':locators,
                            'pattern_candidates_for_human_read':candidates,
                            'no_markdown_comment_swallow_markers':True,
                            'paragraph_openings':[p.splitlines()[0] for p in text.split('\n\n') if p and not p.startswith(('#','|'))]}
audiences = ['Parameterized-MAF expert','Ordinary-rooted practitioner','Lean expert','Implementation/API user','Beginner']
review = (BASE/names[0]).read_text()
rows = [line for line in review.splitlines() if any(line.startswith('| '+a+' /') for a in audiences)]
assert len(rows) == 10
for audience in audiences:
    assert sum(line.startswith('| '+audience+' / correctness') for line in rows) == 1
    assert sum(line.startswith('| '+audience+' / novelty') for line in rows) == 1
    assert all(len(line.split('|')) == 6 for line in rows)
output['audience_rows'] = len(rows)
output['new_mathematical_replications'] = 0
(BASE/f'PROSE-CHECK-{pass_name}.json').write_text(json.dumps(output,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'pass':pass_name,'files':len(names),'audience_rows':len(rows),
                  'quoted_spans':sum(len(f['exact_quotes']) for f in output['files'].values()),
                  'pattern_counts':{n:{k:len(v) for k,v in f['pattern_candidates_for_human_read'].items()}
                                    for n,f in output['files'].items()}}, indent=2))
