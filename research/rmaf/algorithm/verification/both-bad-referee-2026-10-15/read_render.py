"""One-shot HTML-to-text extraction for local rendered-prose linting."""
from html.parser import HTMLParser
from pathlib import Path
import json

class Text(HTMLParser):
    def __init__(self):
        super().__init__()
        self.parts = []
        self.skip = False
        self.rows = 0
    def handle_starttag(self, tag, attrs):
        if tag in ('head','style'):
            self.skip = True
        if tag == 'tr':
            self.rows += 1
    def handle_endtag(self, tag):
        if tag in ('head','style'):
            self.skip = False
        if tag in ('p','h1','h2','h3','tr'):
            self.parts.append('\n\n')
        if tag in ('td','th'):
            self.parts.append(' | ')
    def handle_data(self, data):
        if not self.skip:
            self.parts.append(data)

out = Path(__file__).resolve().parent
result = []
for name in ['REPORT','COMPANION-PROPOSED-v1','SOURCE-LEDGER-v1']:
    p = Text()
    p.feed((out/(name+'.html')).read_text())
    text = ''.join(p.parts)
    (out/(name+'.rendered.txt')).write_text(text)
    result.append({'name':name,'table_rows_including_headers':p.rows,'html_to_text':'complete'})
assert result[0]['table_rows_including_headers'] == 19
assert result[1]['table_rows_including_headers'] == 0
(out/'RENDER-CHECK-v1.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
