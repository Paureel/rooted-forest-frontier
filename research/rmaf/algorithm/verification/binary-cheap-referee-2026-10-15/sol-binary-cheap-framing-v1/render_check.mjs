// One-shot local Markdown render/quote check for this framing report only.
// Existing marked renderer is reused; no scientific calculation is performed.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { marked } from '/Users/paurel/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/marked/lib/marked.esm.js';
const own = path.dirname(new URL(import.meta.url).pathname);
const root = '/Users/paurel/Documents/ChatGPT/bootscience';
const author = path.join(root, 'research/rmaf/algorithm/universal233/binary_cheap');
const review = path.join(root, 'research/rmaf/algorithm/verification/binary-cheap-2026-10-15/sol-review-CONFIRMED-v1/review');
const corpus = ['RESULT.md','INTERFACE.md','FIRST-GAP.md'].map(p=>fs.readFileSync(path.join(author,p),'utf8')).concat(['FINAL-REPORT-v1.md','ERRATUM-ORIGIN-AUDIT-v1.md'].map(p=>fs.readFileSync(path.join(review,p),'utf8')));
const reports=[];
for (const file of ['referee_sim_binary_cheap.md','COMPANION-SCOPE-NOTE-v1.md','READING-CONTACT-LEDGER-v1.md','LINT-RECORD-v1.md']) {
  const src=fs.readFileSync(path.join(own,file),'utf8');
  const tokens=marked.lexer(src,{gfm:true});
  const html=marked.parse(src,{gfm:true});
  const quotes=[...src.matchAll(/“([^”]+)”/g)].map(m=>m[1]);
  const missingQuotes=quotes.filter(q=>!corpus.some(s=>s.includes(q)));
  if(missingQuotes.length)throw Error(JSON.stringify({file,missingQuotes}));
  const links=[...src.matchAll(/\]\((\/[^)]+)\)/g)].map(m=>m[1]);
  const missingLinks=links.filter(p=>!fs.existsSync(p));
  if(missingLinks.length)throw Error(JSON.stringify({file,missingLinks}));
  const tables=tokens.filter(t=>t.type==='table').map(t=>t.rows.length);
  if(file==='referee_sim_binary_cheap.md' && JSON.stringify(tables)!==JSON.stringify([6,10,7]))throw Error(`table rows ${tables}`);
  fs.writeFileSync(path.join(own,file.replace('.md','.html')),`<!doctype html><html><head><meta charset="utf-8"><style>body{font:16px/1.5 sans-serif;margin:2rem;max-width:110rem}table{border-collapse:collapse}td,th{border:1px solid #bbb;padding:.5rem;vertical-align:top}code{overflow-wrap:anywhere}</style></head><body>${html}</body></html>\n`);
  reports.push({file,sha256:crypto.createHash('sha256').update(src).digest('hex'),tables,verbatim_quotes:quotes.length,all_quoted_spans_in_sources:missingQuotes.length===0,local_links:links.length,all_local_links_exist:missingLinks.length===0});
}
fs.writeFileSync(path.join(own,'render-quote-checks-v1.json'),JSON.stringify({scope:'Markdown parse, table structure, quote and path checks only',reports},null,2)+'\n');
console.log(JSON.stringify(reports,null,2));
