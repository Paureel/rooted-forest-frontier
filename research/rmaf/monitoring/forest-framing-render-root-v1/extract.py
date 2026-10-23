"""Extract local rendered HTML text for editorial reading, without execution."""
from html.parser import HTMLParser
from pathlib import Path
import json

class Text(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.parts = []
        self.rows = 0
    def handle_starttag(self, tag, attrs):
        if tag == 'tr':
            self.rows += 1
    def handle_endtag(self, tag):
        if tag in ('p', 'h1', 'h2', 'h3', 'tr', 'li'):
            self.parts.append('\n\n')
        elif tag in ('td', 'th'):
            self.parts.append(' | ')
    def handle_data(self, data):
        self.parts.append(data)

base = Path(__file__).resolve().parent
def extract(name):
    p = Text()
    p.feed((base / (name + '.html')).read_text(encoding='utf8'))
    return ''.join(p.parts), p.rows

control, rows = extract('control')
assert 'c≥2; beforeafter.' in control and rows == 2
assert 'hidden' not in control
corrupt = Text()
corrupt.feed('<p>c≥2; before.</p>')
assert 'c≥2; beforeafter.' not in ''.join(corrupt.parts)
records = []
for name in ['REVIEW-REPORT-v1', 'SCOPE-COMPANION-v1']:
    text, rows = extract(name)
    (base / (name + '.rendered.txt')).write_text(text, encoding='utf8')
    records.append({'name': name, 'table_rows_including_headers': rows})
assert records[0]['table_rows_including_headers'] == 19
assert records[1]['table_rows_including_headers'] == 0
(base / 'render-check.json').write_text(json.dumps({'control': 'PASS', 'corrupted_missing_tail_caught': True, 'documents': records, 'visual_layout_inspected': False}, indent=2) + '\n')
print(json.dumps(records))
