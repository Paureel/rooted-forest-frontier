// One-shot local Markdown render using the existing bundled marked library.
// This wraps a renderer; it performs no scientific or mathematical checking.
const fs = require('fs');
const path = require('path');
const { marked } = require('/Users/paurel/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/marked');
const dir = __dirname;
const toy = marked.parse('# Heading\n\nText < 3.\n\n|A|B|\n|---|---|\n|1|2|\n');
if (!toy.includes('<h1>Heading</h1>') || !toy.includes('<table>') || !toy.includes('Text &lt; 3.')) throw Error('renderer toy failed');
for (const name of ['REPORT','COMPANION-PROPOSED-v1','SOURCE-LEDGER-v1']) {
  const md = fs.readFileSync(path.join(dir, name+'.md'),'utf8');
  const body = marked.parse(md);
  fs.writeFileSync(path.join(dir,name+'.html'), '<!doctype html><html><head><meta charset="utf-8"><title>'+name+'</title><style>body{font:16px/1.5 system-ui;max-width:1400px;margin:40px auto;padding:0 20px}table{border-collapse:collapse}th,td{border:1px solid #bbb;padding:9px;vertical-align:top}code{font-size:0.86em;overflow-wrap:anywhere}a{overflow-wrap:anywhere}</style></head><body>'+body+'</body></html>');
}
console.log('Existing renderer known-answer heading/escape/table control passed; three local HTML files written.');
