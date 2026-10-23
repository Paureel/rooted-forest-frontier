#!/usr/bin/env python3
"""One-shot rendered-prose and literal-quotation checks for this review.

Uses existing marked output and standard HTMLParser, not a scientific solver.
Semantic/colleague review remains a separate human-style reading by the agent.
"""
from html.parser import HTMLParser
import json
from pathlib import Path
import re

BASE=Path(__file__).resolve().parent
ROOT=BASE.parents[4]
class Text(HTMLParser):
    def __init__(self):
        super().__init__(); self.parts=[]; self.rows=[]; self.row=None
    def handle_starttag(self,tag,attrs):
        if tag in {'p','tr','h1','h2','h3','li'}: self.parts.append('\n')
        if tag=='tr': self.row=0
        if tag in {'td','th'}:
            self.row += 1; self.parts.append('\t')
    def handle_endtag(self,tag):
        if tag=='tr': self.rows.append(self.row); self.row=None
        if tag in {'p','tr','h1','h2','h3','li'}: self.parts.append('\n')
    def handle_data(self,data): self.parts.append(data)

toy=Text(); toy.feed('<p>A <code>x</code> B.</p><table><tr><td>1</td><td>2</td></tr></table>')
assert 'A x B.' in ''.join(toy.parts) and toy.rows==[2]
assert 'missing quote' not in 'A x B.'
rendered={}
for name in ['referee_sim_final_cuts','PROPOSED-ADDITIONS']:
    parser=Text(); parser.feed((BASE/(name+'.html')).read_text())
    text=''.join(parser.parts)
    (BASE/(name+'.rendered.txt')).write_text(text)
    rendered[name]={'table_column_counts':parser.rows,
      'lowercase_after_period_candidates':re.findall(r'.{0,65}\. [a-z]{3,}.{0,65}',text),
      'paragraph_openings':[x.strip().split('. ')[0] for x in text.split('\n\n') if x.strip()]}
assert rendered['referee_sim_final_cuts']['table_column_counts']==[5]*11+[3]*9
srcs=['research/rmaf/algorithm/universal233/final_cut_recovery/'+x for x in
      ['RESULT.md','INTERFACE.md','FIRST-GAP.md']]
srcs += ['research/rmaf/algorithm/verification/final-cuts-2026-10-15/'+x for x in
         ['RESULT.md','CONSUMER-TRACE.md','SOURCE-COST-REVIEW.md','INSTRUMENT-HISTORY.md']]
source_texts={p:(ROOT/p).read_text() for p in srcs}
quotes=[]
report=(BASE/'referee_sim_final_cuts.md').read_text()
imagined={q for line in report.splitlines()
          if '| Correctness |' in line or '| Novelty |' in line
          for q in re.findall('“([^”]+)”',line.split('|')[3])}
assert len(imagined)==10
for q in re.findall('“([^”]+)”',report):
    if q in imagined:
        quotes.append({'quote':q,'class':'imagined audience objection'})
    else:
        hits=[{'path':p,'line':i+1} for p,t in source_texts.items()
              for i,line in enumerate(t.splitlines()) if q in line]
        assert hits, q
        quotes.append({'quote':q,'class':'literal source excerpt','locations':hits})
(BASE/'PROSE-MACHINE-CHECK.json').write_text(json.dumps({
 'scope':'render/text/quotation check only; no semantic or mathematical certification',
 'synthetic_parser_control':True,'table_shape_checked':True,'quotes':quotes,
 'rendered':rendered},indent=2)+'\n')
print(json.dumps({'quote_occurrences':len(quotes),'table_shape_checked':True,
                  'source_quotes_literal':True,'rendered_texts':len(rendered)}))
