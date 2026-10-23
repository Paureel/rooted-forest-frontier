"""One-use quote/locator/render-text check; human lint is recorded separately.

Emitall GUIDE was consulted. Its TeX seam check does not apply to Markdown;
this small check retrieves exact local quoted lines and rendered HTML text.
"""
from pathlib import Path
from html.parser import HTMLParser
import json
import re

OUT = Path(__file__).resolve().parent
ROOT = Path(__file__).resolve().parents[5]
ALG = ROOT / 'research/rmaf/algorithm'
BASE = ALG / 'verification/output-state-2026-10-15/frozen-review-v1/review-v1'
SOURCES = {
    'R': ALG / 'universal233/output_state/RESULT.md',
    'I': ALG / 'universal233/output_state/INTERFACE.md',
    'G': ALG / 'universal233/output_state/FIRST-GAP.md',
    'S': BASE / 'SEMANTIC-REVIEW-v1.md',
    'C': BASE / 'CONSUMER-TRACE-v2.md',
    'W': BASE / 'RUNTIME-REVIEW-v1.md',
    'P': BASE / 'CONTACTS-AND-CORRECTIONS-v1.md',
    'Tree': BASE / 'isolated-source-v1/RMAF.lean',
}


def require_quote(line, quote):
    if quote not in line:
        raise ValueError('quotation does not occur verbatim')


# Mechanical controls follow document contact, hence no blind credit.
require_quote('known exact text', 'exact')
try:
    require_quote('known exact text', 'invented')
except ValueError:
    corrupted_quote_caught = True
else:
    raise AssertionError('quotation checker failed corruption control')

quotes = [
    ('R',3,'a conditional reconstruction from the whole current B forest'),
    ('G',5,'The consumer assumes that exact child-specific contract.'),
    ('C',16,'an actual positive FB answer'),
    ('C',16,'q0 generation budget remains distinct.'),
    ('R',3,'A full solver, global runtime, original cut-address reconstruction, and novelty remain outside this result.'),
    ('S',43,'smaller base and novelty remain OPEN.'),
    ('I',3,'The reconstructed object is a labelled agreement forest.'),
    ('I',14,'Original target embeddings are checked on F inside `ForestState.agrees`'),
    ('C',18,'It is an edge in the restricted A source.'),
    ('G',7,'whole-original source cut set'),
    ('G',7,'no full solver or novelty claim is made here.'),
    ('S',3,'This review adds zero independent replications beyond the disclosed existing checker lineage.'),
    ('S',11,'No other body adaptation was accepted.'),
    ('P',15,'The structural body hash is a diagnostic, not a cryptographic body equivalence certificate.'),
    ('P',7,'explicitly post-contact'),
    ('S',13,'Independent semantic reconstruction'),
    ('S',43,'Full well-founded residual solving'),
    ('R',7,'supply no independent certification.'),
    ('C',6,'Proper S and checked Q give no dropped entry'),
    ('C',16,'exact child-specific whole-Bforest contract at q-1'),
    ('W',3,'evaluated once'),
    ('W',7,'repeated invocations must each be charged.'),
    ('C',18,"that caller's original guards."),
    ('W',3,'No compiled instruction correspondence or recursive solver runtime theorem has been established.'),
    ('W',11,'No whole-algorithm recurrence or base bound follows from this source-work account.'),
    ('R',3,'pending fresh nonauthor verification'),
    ('S',3,'NONAUTHOR-CONFIRMED for the released output-state interface, with its printed hypotheses'),
    ('C',24,'Algorithm, Correctness and Smaller-base remain OPEN.'),
    ('Tree',27,'No orientation of siblings is part of a phylogenetic tree.'),
    ('Tree',83,'Empty selections give none; unary vertices are suppressed.'),
    ('S',21,'target-overlapping Q admits a suitable refining F but rejects F=Q'),
    ('S',41,'not additional blind verification credit'),
]
records = []
for key, number, quote in quotes:
    line = SOURCES[key].read_text().splitlines()[number-1]
    require_quote(line, quote)
    records.append({'path': str(SOURCES[key].relative_to(ROOT)), 'line': number, 'quote': quote})

report = (OUT / 'referee_sim_output_state.md').read_text()
locators = []
for key, number in re.findall(r'\b([RIGSCWP]):(\d+)', report):
    number = int(number)
    assert 1 <= number <= len(SOURCES[key].read_text().splitlines())
    locators.append([key, number])
audience_rows = [line for line in report.splitlines() if line.startswith('| ') and ('| Correctness:' in line or '| Novelty:' in line)]
assert len(audience_rows) == 10
assert sum('| Correctness:' in x for x in audience_rows) == 5
assert sum('| Novelty:' in x for x in audience_rows) == 5


class TextReader(HTMLParser):
    def __init__(self):
        super().__init__()
        self.parts = []
        self.hide = 0
    def handle_starttag(self, tag, attrs):
        if tag in ('style','script','title'):
            self.hide += 1
        if tag in ('p','h1','h2','tr'):
            self.parts.append('\n')
    def handle_endtag(self, tag):
        if tag in ('style','script','title'):
            self.hide -= 1
        if tag in ('p','h1','h2','tr'):
            self.parts.append('\n')
    def handle_data(self, data):
        if not self.hide:
            self.parts.append(data)


render_records = []
for stem in ('referee_sim_output_state','PROPOSED-SCOPE-NOTE-v1'):
    html = (OUT / (stem+'.html')).read_text()
    parser = TextReader()
    parser.feed(html)
    text = ''.join(parser.parts)
    (OUT / (stem+'.rendered.txt')).write_text(text)
    md = (OUT / (stem+'.md')).read_text()
    assert '<!--' not in md
    assert 'OPEN' in text
    assert 'q−1' in text or 'q-1' in text
    if stem == 'referee_sim_output_state':
        for _,_,quote in quotes:
            assert quote.replace('`','') in text
    render_records.append({'name':stem,'rendered_characters':len(text),
                           'lowercase_after_period_candidates':re.findall(r'.{0,60}\. [a-z]{3,}.{0,60}',text)})

result = {'verdict':'PASS_QUOTE_LOCATOR_AND_RENDER_TEXT_CHECKS',
          'not_a_human_prose_or_theorem_check':True,
          'post_contact_control':{'clean_quote':True,'altered_quote_rejected':corrupted_quote_caught},
          'quote_count':len(records),'quotes':records,'locator_count':len(locators),
          'audience_correctness_rows':5,'audience_novelty_rows':5,
          'renders':render_records}
(OUT/'PROSE-CHECKS-v1.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('verdict','quote_count','locator_count','audience_correctness_rows','audience_novelty_rows')},indent=2))
