// Local text-render inspection only; no mathematical or source-proof checking.
const fs = require('fs');
const path = require('path');
const { marked } = require('/Users/paurel/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/marked');
const toy = marked.parse('# Heading\n\nc≥2; before<!--hidden-->after.\n\n|A|B|\n|---|---|\n|1|2|\n');
if (!toy.includes('<h1>Heading</h1>') || !toy.includes('<table>') || !toy.includes('c≥2; before<!--hidden-->after.')) throw Error('render control failed');
fs.writeFileSync(path.join(__dirname, 'control.html'), toy, 'utf8');
for (const name of ['REVIEW-REPORT-v1', 'SCOPE-COMPANION-v1']) {
  const input = path.resolve('research/rmaf/algorithm/verification/forest-solver-referee-2026-10-15/sol-reader-v1', name + '.md');
  const body = marked.parse(fs.readFileSync(input, 'utf8'));
  fs.writeFileSync(path.join(__dirname, name + '.html'), body, 'utf8');
}
