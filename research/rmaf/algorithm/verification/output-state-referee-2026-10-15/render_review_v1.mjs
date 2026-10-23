// One-use local Markdown render for this frame review. Uses bundled marked;
// no hosting, upload, browser network request, or scientific calculation.
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { marked } from '/Users/paurel/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/marked/lib/marked.esm.js';

const here = path.dirname(fileURLToPath(import.meta.url));
const names = ['referee_sim_output_state', 'PROPOSED-SCOPE-NOTE-v1'];
for (const name of names) {
  const source = fs.readFileSync(path.join(here, name + '.md'), 'utf8');
  const html = '<!doctype html><html lang="en"><meta charset="utf-8"><title>' + name +
    '</title><style>body{font:16px/1.5 system-ui;max-width:1200px;margin:2rem auto;padding:1rem}table{border-collapse:collapse}th,td{border:1px solid #ccc;padding:.5rem;vertical-align:top}code{overflow-wrap:anywhere}</style><body>' +
    marked.parse(source, { gfm: true }) + '</body></html>\n';
  fs.writeFileSync(path.join(here, name + '.html'), html);
  console.log(name + ': local HTML rendered');
}
