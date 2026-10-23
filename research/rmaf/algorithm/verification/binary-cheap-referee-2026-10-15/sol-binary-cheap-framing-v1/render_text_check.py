"""One-shot HTML text extraction for the local two-pass prose review only."""
from html.parser import HTMLParser
from pathlib import Path
import json
import re

class Text(HTMLParser):
    def __init__(self):
        super().__init__()
        self.parts=[]
        self.hidden=False
    def handle_starttag(self,tag,attrs):
        if tag in ['style','script']:
            self.hidden=True
        if tag in ['p','tr','h1','h2','td','th']:
            self.parts.append('\n')
    def handle_endtag(self,tag):
        if tag in ['style','script']:
            self.hidden=False
        if tag in ['p','tr','h1','h2','td','th']:
            self.parts.append('\n')
    def handle_data(self,data):
        if not self.hidden:
            self.parts.append(data)

own=Path(__file__).resolve().parent
checks=[]
for name in ['referee_sim_binary_cheap','COMPANION-SCOPE-NOTE-v1','READING-CONTACT-LEDGER-v1','LINT-RECORD-v1']:
    parser=Text()
    parser.feed((own/(name+'.html')).read_text())
    text=''.join(parser.parts)
    text=re.sub(r'\n[ \t]*\n+', '\n\n',text)
    (own/(name+'.rendered.txt')).write_text(text)
    lower=[text[max(0,m.start()-35):m.end()+65] for m in re.finditer(r'\. [a-z]{3,}',text)]
    checks.append({'file':name,'lowercase_after_period_candidates':lower,'html_text_extracted':True})
(own/'render-text-checks-v1.json').write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps(checks,indent=2))
