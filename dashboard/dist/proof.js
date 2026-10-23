'use strict';
// Evidence is supplied by local campaign checkpoints. Status is never inferred from CPU or exit codes.
const P = {key:null,example:0,block:null,examples:[],routes:[],nodes:[],graphAll:false};
const proofColors = {checked:'#338b78',tested:'#5978bd',open:'#bc9550',conditional:'#bc9550',pending:'#9ba7ae',running:'#5978bd',refuted:'#be7275','source-reported':'#5978bd',complete:'#8d979e'};
const proofNames = {checked:'Checked',tested:'Tested',open:'Open',conditional:'Conditional',pending:'Pending',running:'Working',refuted:'Refuted','source-reported':'Source reported',complete:'Recorded'};
const forestColors = ['#338b78','#5978bd','#c18f55','#a281af','#c17380','#6b9bba','#969d54'];
function proofBadge(state){return `<span class="proof-state ${esc(state)}">${esc(proofNames[state]||state)}</span>`;}
function proofDetail(record,kind='ROUTE'){
  const sources=(record.sources||[]).filter(s=>/^https?:\/\//.test(s.url||''));
  drawer(kind,`<h2 id="drawerTitle">${esc(record.title||record.label||record.id)}</h2>${proofBadge(record.status)}<p>${esc(record.detail||record.summary||'')}</p>${record.metrics?Object.entries(record.metrics).map(([k,v])=>`<div class="drawer-meta"><span>${esc(k.replaceAll('_',' '))}</span><strong>${esc(typeof v==='object'?JSON.stringify(v):v)}</strong></div>`).join(''):''}${(record.claims||[]).map(c=>`<div class="proof-claim">${proofBadge(c.status)}<strong>${esc(c.label)}</strong><p>${esc(c.detail)}</p></div>`).join('')}${record.next?`<div class="drawer-callout">${esc(record.next)}</div>`:''}${sources.length?'<details open><summary>Sources</summary>'+sources.map(s=>`<a class="proof-source" href="${esc(s.url)}" target="_blank" rel="noopener noreferrer">${esc(s.title||s.url)} ↗</a><div class="source-locator">${esc(s.locator||'')}</div>`).join('')+'</details>':''}${(record.artifacts||[]).length?'<details open><summary>Evidence</summary>'+record.artifacts.map(f=>`<button class="proof-file" data-proof-file="${esc(typeof f==='string'?f:f.path)}">${esc(typeof f==='string'?f:f.path)}</button>`).join('')+'</details>':''}`);
  $('drawerContent').querySelectorAll('[data-proof-file]').forEach(b=>b.onclick=()=>openProofFile(b.dataset.proofFile));
}
async function openProofFile(path){
  drawer('EVIDENCE',`<h2 id="drawerTitle">${esc(path.split('/').at(-1))}</h2><pre id="proofFileText">Loading…</pre>`);
  const target=$('proofFileText');
  try{const r=await fetch('/api/proof/file?path='+encodeURIComponent(path));const d=await r.json();target.textContent=r.ok?d.text:d.error;}catch(e){target.textContent='Connection unavailable';}
}
function proofFlow(routes){
  const steps=[['Read','baseline'],['Enumerate','oracle'],['Explore','branching'],['Challenge','verification'],['Formalize','setup']];
  const positions=steps.map((_,i)=>55+i*183);
  $('proofFlow').innerHTML=steps.map(([label,id],i)=>{
    const r=routes.find(x=>x.id===id);const state=r?.status||'pending';
    return `${i?`<path d="M${positions[i-1]+23} 40H${positions[i]-23}" stroke="#e2e9eb"/>`:''}<g class="proof-step" tabindex="0" role="button" data-proof-route="${esc(id)}" aria-label="${label}: ${esc(proofNames[state]||state)}" transform="translate(${positions[i]},40)"><circle r="21" fill="#fff" stroke="${proofColors[state]||'#9ba7ae'}" stroke-width="1.4"/><text y="4" text-anchor="middle" fill="${proofColors[state]||'#9ba7ae'}" font-size="12">${i+1}</text><text y="43" text-anchor="middle" fill="#72858e" font-size="12">${label}</text></g>`;
  }).join('');
  bindProofNodes($('proofFlow'), 'proofRoute',id=>proofDetail(routes.find(r=>r.id===id)||{id,title:steps.find(x=>x[1]===id)?.[0],status:'pending',summary:'No checkpoint recorded.'}));
}
function bindProofNodes(el,key,callback){el.querySelectorAll(`[data-${key.replace(/[A-Z]/g,m=>'-'+m.toLowerCase())}]`).forEach(n=>{n.onclick=()=>callback(n.dataset[key]);n.onkeydown=e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();callback(n.dataset[key]);}};});}
function lemmaGraph(routes,spec){
  const nodes=[{id:'baseline-bound',label:'Published bound',status:spec.baseline.status,detail:'Reported bound: O*(2.3391^k). The current literature-audit checkpoint records its coverage and gaps.',sources:[{title:'Split-or-decompose',url:spec.baseline.url}]}];
  routes.forEach(r=>(r.lemmas||[]).forEach(l=>nodes.push({...l,route:r.id,artifacts:l.artifacts||r.artifacts,sources:l.sources||r.sources})));
  routes.forEach(r=>(r.claims||[]).filter(c=>c.status==='refuted'&&!nodes.some(n=>n.id===c.id)).forEach(c=>nodes.push({...c,route:r.id,artifacts:r.artifacts,sources:r.sources})));
  if(!P.graphAll){
    const focus=[nodes[0]];
    const preferred={'baseline':'whidden-transfer','decomposition':'mark-propagate','formal':'formal-semantics','previous-work':'safe-cover'};
    routes.forEach(r=>{const n=nodes.find(n=>n.id===preferred[r.id])||nodes.find(n=>n.route===r.id&&['open','conditional'].includes(n.status));if(n)focus.push(n);});
    nodes.splice(0,nodes.length,...focus);
  }
  nodes.push({id:'improved-algorithm',label:'Improved algorithm',status:'open',detail:spec.target+' No unconditional improvement has been certified.',depends_on:['baseline-bound',...nodes.filter(n=>n.status==='open'||n.status==='conditional').map(n=>n.id)]});
  // Explicit dependencies only. The target also records its outstanding obligations.
  const ids=new Set(nodes.map(n=>n.id));const depths={};
  function depth(n,visiting=new Set()){
    if(depths[n.id]!=null)return depths[n.id];if(visiting.has(n.id))return 0;
    const seen=new Set(visiting);seen.add(n.id);
    return depths[n.id]=Math.min(3,Math.max(-1,...(n.depends_on||[]).filter(id=>ids.has(id)).map(id=>depth(nodes.find(x=>x.id===id),seen)))+1);
  }
  nodes.forEach(n=>depth(n));const columns=[[],[],[],[]];nodes.forEach(n=>columns[depths[n.id]].push(n));
  const maxCount=Math.max(...columns.map(c=>c.length),1),height=Math.max(250,maxCount*72+30);const positions={};
  columns.forEach((col,i)=>col.forEach((n,j)=>positions[n.id]={x:108+i*207,y:(j+.5)*height/col.length}));
  $('lemmaGraph').setAttribute('viewBox',`0 0 850 ${height}`);$('lemmaGraph').style.maxHeight=Math.max(280,height)+'px';
  $('lemmaGraph').innerHTML=nodes.map(n=>(n.depends_on||[]).filter(id=>positions[id]).map(id=>{const a=positions[id],b=positions[n.id];return `<path d="M${a.x+78} ${a.y}C${a.x+125} ${a.y},${b.x-125} ${b.y},${b.x-78} ${b.y}" fill="none" stroke="#e1e8eb"/>`;}).join('')).join('')+nodes.map(n=>{
    const p=positions[n.id],c=proofColors[n.status]||'#9ba7ae';const words=(n.label||n.id).split(' ');const lines=[];let line='';for(const w of words){if((line+' '+w).length>21&&line){lines.push(line);line=w;}else line+=(line?' ':'')+w;}lines.push(line);
    return `<g class="lemma-node" tabindex="0" role="button" data-proof-lemma="${esc(n.id)}" transform="translate(${p.x},${p.y})" aria-label="${esc(n.label)}: ${esc(proofNames[n.status]||n.status)}"><rect x="-78" y="-26" width="156" height="52" rx="9" fill="#fff" stroke="#e4eaed"/><circle cx="-65" cy="-15" r="3" fill="${c}"/>${lines.slice(0,2).map((l,i)=>`<text x="0" y="${i*13-(lines.length>1?3:0)}" text-anchor="middle" font-size="10" fill="#637984">${esc(l)}</text>`).join('')}<text y="18" text-anchor="middle" font-size="8" fill="${c}">${esc(proofNames[n.status]||n.status)}</text></g>`;
  }).join('');P.nodes=nodes;bindProofNodes($('lemmaGraph'),'proofLemma',id=>proofDetail(nodes.find(n=>n.id===id),'LEMMA'));
}
function drawForest(){
  const ex=P.examples[P.example];
  if(!ex){$('forestSvg').innerHTML='<text x="255" y="140" text-anchor="middle" fill="#a2afb5" font-size="12">Waiting for an exact witness</text>';$('forestBlocks').innerHTML='';$('forestCaption').textContent='';return;}
  const blocks=ex.forest||[];
  function tree(t,origin){
    const leaves=[];const nodes=[];const edges=[];
    function visit(t,parent=null,depth=0){const n={id:nodes.length,parent,depth,label:Array.isArray(t)?null:String(t),children:[]};nodes.push(n);if(Array.isArray(t)){n.children=t.map(x=>visit(x,n,depth+1));}else leaves.push(n);return n;}
    const root=visit(t),maxDepth=Math.max(...nodes.map(n=>n.depth),1);leaves.forEach((n,i)=>n.x=origin+24+i*194/Math.max(1,leaves.length-1));
    function pos(n){n.children.forEach(pos);if(n.children.length)n.x=n.children.reduce((s,c)=>s+c.x,0)/n.children.length;n.y=48+n.depth/maxDepth*162;if(n.parent)edges.push([n.parent,n]);}pos(root);
    let svg=edges.map(([a,b])=>`<path d="M${a.x} ${a.y}V${b.y}H${b.x}" stroke="#dde5e9" fill="none" stroke-width="1.3"/>`).join('');
    blocks.forEach((block,i)=>{
      const chosen=leaves.filter(n=>block.map(String).includes(n.label));if(chosen.length<2)return;
      const chains=chosen.map(n=>{const p=[];for(let cur=n;cur;cur=cur.parent)p.push(cur);return p;});
      const lca=chains[0].find(n=>chains.every(c=>c.includes(n)));const highlighted=new Set();chains.forEach(c=>{for(const n of c){if(n===lca)break;highlighted.add(n);}});
      const opacity=P.block==null||P.block===i?1:.15;highlighted.forEach(n=>{svg+=`<path d="M${n.parent.x} ${n.parent.y}V${n.y}H${n.x}" stroke="${forestColors[i%forestColors.length]}" fill="none" stroke-width="2.6" opacity="${opacity}"/>`;});
    });
    svg+=nodes.map(n=>{const i=blocks.findIndex(b=>b.map(String).includes(n.label));return n.label==null?`<circle cx="${n.x}" cy="${n.y}" r="2" fill="#9cafb7"/>`:`<g tabindex="0" role="button" data-forest-block="${i}" aria-label="Leaf ${esc(n.label)}, component ${i+1}"><circle cx="${n.x}" cy="${n.y}" r="5" fill="${forestColors[Math.max(0,i)%forestColors.length]}" opacity="${P.block==null||P.block===i?1:.22}"/><text x="${n.x}" y="${n.y+20}" text-anchor="middle" font-size="11" fill="#738791">${esc(n.label)}</text></g>`;}).join('');return svg;
  }
  $('forestSvg').innerHTML='<text x="125" y="24" text-anchor="middle" fill="#a0acb3" font-size="10">T₁</text><text x="380" y="24" text-anchor="middle" fill="#a0acb3" font-size="10">T₂</text><path d="M255 36V235" stroke="#f0f3f5"/>'+tree(ex.tree_a,0)+tree(ex.tree_b,255);
  $('forestBlocks').innerHTML=blocks.map((b,i)=>`<button data-block="${i}" class="${P.block===i?'active':''}" aria-label="Highlight component ${i+1}" style="--block:${forestColors[i%forestColors.length]}"><i></i>${esc(b.join(' · '))}</button>`).join('')+`<span>k = ${esc(ex.k??blocks.length)}</span>`;
  const select=i=>{P.block=P.block===i?null:i;drawForest();};$('forestBlocks').querySelectorAll('[data-block]').forEach(b=>b.onclick=()=>select(Number(b.dataset.block)));$('forestSvg').querySelectorAll('[data-forest-block]').forEach(n=>{n.onclick=()=>select(Number(n.dataset.forestBlock));n.onkeydown=e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();n.onclick();}};});
  $('forestCaption').textContent=ex.caption||'Exact witness · select a component';
}
window.renderProof=function(){
  const visible=S.mode==='proof';$('proofView').hidden=!visible;document.querySelector('.main-grid').hidden=visible;
  const map=document.querySelector('.map-panel');if(!P.mapHome){P.mapHome=document.createComment('toolkit');map.before(P.mapHome);}
  if(visible&&map.parentElement!==$('proofMapSlot'))$('proofMapSlot').append(map);
  if(!visible&&map.parentElement===$('proofMapSlot'))P.mapHome.after(map);
  if(!visible)return;$('runTitle').textContent='Rooted MAF';
  const proof=S.snapshot?.proof;if(!proof){$('proofFreshness').textContent='Waiting for campaign';return;}
  $('proofFreshness').textContent=S.online?`Live · ${clock(proof.at)}`:'Disconnected · last checkpoint';
  const key=JSON.stringify([proof.spec,proof.routes,proof.history,proof.errors]);if(P.key===key)return;P.key=key;P.routes=proof.routes||[];
  proofFlow(P.routes);lemmaGraph(P.routes,proof.spec);
  const checked=P.routes.filter(r=>['setup','formal'].includes(r.id)).reduce((n,r)=>n+Number(r.metrics?.checked_theorems||0),0);
  const oracle=P.routes.find(r=>r.id==='oracle');const cases=oracle?.metrics?.pairs_checked??oracle?.metrics?.pairs??oracle?.metrics?.instances??oracle?.metrics?.tree_pairs??'—';
  const sources=new Set(P.routes.flatMap(r=>(r.sources||[]).map(s=>s.url))).size;
  $('proofCounts').innerHTML=[['Journal baseline','2.3391','reported'],['Pairs',cases,'exact'],['Lean theorems',checked,'checked'],['Sources',sources,'linked']].map(([label,value,unit])=>`<div class="readout"><div class="readout-label">${label}</div><div class="readout-value">${esc(value)}<small>${unit}</small></div></div>`).join('');
  const earlier=proof.spec.baseline.earlier_claim;$('baselineCaveat').hidden=!earlier;if(earlier){$('baselineCaveat').textContent='Earlier 2ᵏ thesis claim · under review ↗';$('baselineCaveat').onclick=()=>proofDetail({title:earlier.title,status:'open',detail:earlier.detail,sources:[{title:earlier.title,url:earlier.url,locator:'Chapter 6, Theorems 6.1, 6.12, 6.13'}]},'PRIOR ART');}
  $('proofRoutes').innerHTML=P.routes.map(r=>`<button class="proof-route" data-route="${esc(r.id)}"><span class="route-orbit" style="--route:${proofColors[r.status]||'#8d979e'}"><i></i></span><strong>${esc(r.title)}</strong>${proofBadge(r.status)}</button>`).join('');$('proofRoutes').querySelectorAll('[data-route]').forEach(b=>b.onclick=()=>proofDetail(P.routes.find(r=>r.id===b.dataset.route)));
  const examples=P.routes.flatMap(r=>[...(r.examples||[]),...(r.example?[r.example]:[])].filter(e=>e.tree_a&&e.tree_b).map(e=>({...e,route:r.title})));const exampleKey=JSON.stringify(examples);
  if(P.exampleKey!==exampleKey){P.exampleKey=exampleKey;P.examples=examples;P.example=Math.min(P.example,Math.max(0,examples.length-1));$('forestExample').innerHTML=examples.map((e,i)=>`<option value="${i}">${esc(e.title||e.route)}</option>`).join('');$('forestExample').value=P.example;$('forestExample').hidden=!examples.length;drawForest();}
  $('forestExample').onchange=e=>{P.example=Number(e.target.value);P.block=null;drawForest();};
  const history=proof.history||[];$('proofHistoryCount').textContent=history.length+' observed';$('proofHistory').innerHTML=history.slice(-8).reverse().map((e,i)=>`<button class="proof-history-row" data-checkpoint="${history.length-1-i}"><time>${clock(e.at)}</time><span>${esc(e.record.title)}</span>${proofBadge(e.record.status)}<span>↗</span></button>`).join('');$('proofHistory').querySelectorAll('[data-checkpoint]').forEach(b=>b.onclick=()=>proofDetail(history[Number(b.dataset.checkpoint)].record,'CHECKPOINT'));
  $('proofMeaning').onclick=()=>drawer('PROOF',`<h2 id="drawerTitle">Dependencies</h2><p>Each node is a claim. A line names a dependency. Checked means its recorded check passed; open the node for the exact scope and evidence. Lean counts include formal proofs with recorded build and axiom audits. Tested means finite examples passed; it is not a universal proof. Open and conditional nodes show unfinished obligations. Refuted nodes retain their counterexamples.</p><div class="drawer-callout">The dashboard displays authored checkpoints and links their evidence. It does not independently certify them. No theorem-completion percentage is inferred.</div>`);
  $('proofGraphToggle').textContent=P.graphAll?'Focus':'All nodes';$('proofGraphToggle').onclick=()=>{P.graphAll=!P.graphAll;P.key=null;window.renderProof();};
};
