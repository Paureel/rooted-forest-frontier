'use strict';
const $ = (id) => document.getElementById(id);
const esc = (v = '') => String(v ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const S = {catalog:null,snapshot:null,mode:location.hash==='#proof'?'proof':'auto',selected:null,layer:'tools',query:'',online:false,source:null,historyExpanded:false,demoPlaying:true,demoStep:2,demoOrigin:performance.now()-16000,digits:60,lastFocus:null,drawerFocus:null};
const STAGES = [
  {id:'input',name:'Input',headline:'Set the question',meaning:'Define what to compute and which inputs, conventions, and checks will be used.',demo:'Integrate 4 / (1 + x²) from 0 to 1.',icon:'input'},
  {id:'structure',name:'Structure',headline:'Choose a route',meaning:'Look for equations, singularities, symmetries, or a smaller representation that make the problem tractable.',demo:'A smooth one-dimensional integral can be handled by quadrature.',icon:'shape'},
  {id:'compute',name:'Compute',headline:'Build the answer',meaning:'Run the chosen instruments. Numerical values need error bounds; exact formulas need their own checks.',demo:'Accumulate numerical samples and track an error enclosure.',icon:'compute'},
  {id:'check',name:'Check',headline:'Try to break it',meaning:'Compare against independent work and unused inputs. A process finishing is not a scientific acceptance check.',demo:'Compare separate routes and repeat at higher precision.',icon:'check'},
  {id:'result',name:'Result',headline:'Keep the evidence',meaning:'Save the answer with its inputs, provenance, and check receipts. A missing check stays unreported.',demo:'The toy integral has the exact form π.',icon:'result'},
];
const GATES = [
  {id:'known_truth',name:'Known truth',title:'A check that can fail',meaning:'First recover a known answer. Then corrupt an input deliberately and confirm the pipeline catches it.'},
  {id:'independent',name:'Independent',title:'A separate route',meaning:'Check the answer using code or data that did not help produce it.'},
  {id:'precision',name:'Two precisions',title:'Stable digits',meaning:'Repeat at higher working precision and compare. Stability alone does not prove a rigorous error bound.'},
  {id:'unused',name:'Unused inputs',title:'A fresh test',meaning:'Use inputs that were kept out of fitting or construction. Reusing fit data is not an independent test.'},
];
const DEMO_TOOLS = ['nestor','baller','lockpick','gatekeeper'];
const paths = {input:'M-10-8h20v16h-20ZM-5-3h10m-10 5h7',shape:'M-10 8-5-9 10-3 7 10ZM-5-9 7 10M-10 8 10-3',compute:'M-9-8h18v16h-18ZM-5-3h2m6 0h2M-5 3h2m6 0h2',check:'M-8 0-2 6 9-7',result:'M-8-10H4l5 5V10H-8ZM3-10v6h6M-4 1h9m-9 5h7'};
const arrowSvg = '<svg viewBox="0 0 24 24"><path d="m9 5 7 7-7 7"/></svg>';
const DOM_CACHE = {};
const TERMS = [
  ['certif', 'Certified', 'A checkable error bound or certificate, within the stated assumptions.'],
  ['quadrature', 'Quadrature', 'Approximate an area or total using weighted samples of a function.'],
  ['integral', 'Integral', 'An accumulated area or total described by a function.'],
  ['singular', 'Singularity', 'An input where a function becomes undefined or behaves sharply.'],
  ['basis', 'Basis', 'A smaller set from which the other objects can be built.'],
  ['finite-field', 'Finite field', 'Exact arithmetic performed modulo a prime number.'],
  ['evidence', 'Evidence', 'A model’s probability of the data, averaged over its parameters.'],
  ['period', 'Period', 'A quantity obtained by integrating over a specified path or surface.'],
  ['recurrence', 'Recurrence', 'A rule connecting successive values of a sequence.'],
  ['differential', 'Differential equation', 'An equation linking a function to how it changes.'],
  ['exact', 'Exact', 'Represented without rounding; for example, as an integer or a fraction.'],
];

function currentRun(){
  if(S.mode==='demo') return null;
  const run=S.snapshot?.selected;
  if(S.mode==='history') return run?.id===S.selected ? run : null;
  return run?.status==='running' ? run : null;
}
function isDemo(){return !currentRun() && !['history','proof'].includes(S.mode);}
function effectiveMode(){return S.mode==='proof'?'proof':isDemo()?'demo':S.mode==='history'?'history':'auto';}
function toolById(id){return S.catalog.tools.find(t=>t.id===id)||S.catalog.protocols.find(t=>t.id===id);}
function duration(seconds){if(seconds==null)return '—';seconds=Math.max(0,Math.floor(seconds));if(seconds<3600)return `${Math.floor(seconds/60).toString().padStart(2,'0')}:${(seconds%60).toString().padStart(2,'0')}`;return `${Math.floor(seconds/3600)}h ${Math.floor(seconds%3600/60)}m`;}
function clock(ts){return new Intl.DateTimeFormat('en-GB',{hour:'2-digit',minute:'2-digit',second:'2-digit',timeZone:'Europe/Copenhagen'}).format(new Date(ts*1000));}
function dateLabel(ts){return new Intl.DateTimeFormat('en-GB',{day:'numeric',month:'short',timeZone:'Europe/Copenhagen'}).format(new Date(ts*1000));}
function statusName(state){return ({completed:'Completed',running:'Running',failed:'Failed',partial:'Partial',interrupted:'Interrupted',ended:'Ended · exit unknown'})[state]||state;}

function connect(run=null){
  S.source?.close();
  const source=new EventSource(`/api/events${run?'?run='+encodeURIComponent(run):''}`);
  S.source=source;
  source.onmessage=(event)=>{
    if(source!==S.source)return;
    try{S.snapshot=JSON.parse(event.data);S.online=true;$('startupError').hidden=true;render();}
    catch(error){console.error('Invalid monitor snapshot',error);}
  };
  source.onerror=()=>{if(source!==S.source)return;S.online=false;renderConnection();};
}
function renderConnection(){
  $('connection').classList.toggle('offline',!S.online);
  $('connection').querySelector('span').textContent=S.online?'Connected':'Disconnected';
  $('flowCanvas').classList.toggle('offline',!S.online);
  if(!S.online && currentRun()){$('runBadge').textContent='Last seen';$('runBadge').className='status-badge history';}
}
function setMode(mode,runId=null){
  S.mode=mode;S.selected=runId;
  if(mode==='history')S.selected=runId||S.snapshot?.history.find(r=>r.status!=='running')?.id||'installation';
  connect(mode==='history'?S.selected:null);render();
  if(mode==='history')document.querySelector('.page-heading').scrollIntoView({behavior:'smooth',block:'start'});
}
function demoStep(index){S.demoPlaying=false;S.demoStep=index;S.demoOrigin=performance.now()-index*8000;render();}
function advanceDemo(){
  if(isDemo()&&S.demoPlaying){S.demoStep=Math.floor(((performance.now()-S.demoOrigin)/8000)%5);renderFlow();renderGates();renderPath();renderReadouts();renderChart();renderDemoControls();}
}

function stageStates(run){
  if(isDemo())return Object.fromEntries(STAGES.map((s,i)=>[s.id,i<S.demoStep?'passed':i===S.demoStep?'running':'pending']));
  const states=Object.fromEntries(STAGES.map(s=>[s.id,'unreported']));
  if(!run)return states;
  states.input='passed';
  states.compute=run.status==='running'?'running':run.status==='failed'?'failed':run.status==='interrupted'?'failed':'passed';
  if(run.status!=='running')states.result=run.status==='completed'?'passed':run.status==='failed'?'failed':'unreported';
  for(const [key,event] of Object.entries(run.stages||{}))if(key in states)states[key]=event.state;
  if(run.source==='imported'){states.input='passed';states.compute='passed';states.check='failed';states.result='unreported';}
  return states;
}
function renderFlow(){
  const run=currentRun(),demo=isDemo(),states=stageStates(run);
  let focus=demo?S.demoStep:STAGES.findIndex(s=>states[s.id]==='running');
  if(focus<0)focus=run?.source==='imported'?3:run?.status==='completed'?4:2;
  const positions=[74,237,400,563,726],y=79;
  let html='';
  for(let i=0;i<4;i++){
    const from=positions[i]+34,to=positions[i+1]-34;
    const cls=states[STAGES[i].id]==='passed'&&states[STAGES[i+1].id]==='running'&&S.online?'active':states[STAGES[i].id]==='passed'&&states[STAGES[i+1].id]==='passed'?'passed':'';
    html+=`<path class="flow-link ${cls}" d="M${from} ${y}C${from+35} ${y-16},${to-35} ${y+16},${to} ${y}"/>`;
  }
  html+=STAGES.map((stage,i)=>{
    const state=states[stage.id],cls=state==='running'?'active':state==='passed'?'done':state==='failed'?'failed':'';
    const caption=demo?(i<focus?'ready':i===focus?'explore':''):(state==='unreported'?'unreported':state==='passed'?(stage.id==='result'?'exit 0':'observed'):state==='running'?'active':state==='failed'?'attention':'');
    return `<g class="flow-node ${cls}" data-stage="${i}" role="button" tabindex="0" aria-label="${esc(stage.name)}: ${state}" transform="translate(${positions[i]},${y})"><circle class="outer-ring" r="36"/><circle class="node-ring" r="28"/><path class="flow-icon" d="${paths[stage.icon]}"/>${state==='running'&&S.online?'<circle class="orbit-pulse" cx="29" cy="-22" r="3"/>':''}<text text-anchor="middle" y="64">${stage.name}</text><text class="node-caption" text-anchor="middle" y="84">${caption}</text></g>`;
  }).join('');
  if(DOM_CACHE.flow!==html){
  DOM_CACHE.flow=html;$('flowSvg').innerHTML=html;
  $('flowSvg').querySelectorAll('[data-stage]').forEach(node=>{
    const action=()=>isDemo()?demoStep(Number(node.dataset.stage)):explainStage(Number(node.dataset.stage));
    node.addEventListener('click',action);node.addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();action();}});
  });
  }
  const st=STAGES[focus];
  $('focusLabel').textContent=demo?st.headline:run?.source==='imported'?'Package batteries':focus===4?'Program exited successfully':run?.status==='failed'?'Program returned an error':run?.status==='interrupted'?'Recording ended unexpectedly':run?'Process activity':'Loading run';
  $('focusTool').textContent=demo?(['Input','Quadrature','Nestor + Baller','Gatekeeper','π'][focus]):run?.source==='imported'?'50 checks':run?.tool?toolById(run.tool)?.name||run.tool:'Reported stages only';
}

function demoChart(){
  if(S.demoStep>=3){
    const width=Math.max(15,132-S.digits*1.12),center=468;
    return `<path d="M${center} 33V141" stroke="#c6d6d0" stroke-dasharray="2 5"/><text x="${center}" y="160" text-anchor="middle" fill="#7b9d8d" font-family="serif" font-size="18">π</text><text x="34" y="75" fill="#7b939c" font-family="inherit" font-size="10">Route A</text><text x="34" y="124" fill="#7b939c" font-family="inherit" font-size="10">Route B</text><path d="M${center-width} 71H${center+width}M${center-width} 64v14M${center+width} 64v14" stroke="#76a18d" stroke-width="2"/><path d="M${center-width*.78} 120H${center+width*.93}M${center-width*.78} 113v14M${center+width*.93} 113v14" stroke="#89a2c3" stroke-width="2"/><circle cx="${center-1}" cy="71" r="3" fill="#76a18d"/><circle cx="${center+2}" cy="120" r="3" fill="#89a2c3"/><rect x="${center-width*.78}" y="63" width="${width*1.56}" height="66" rx="3" fill="#afcab5" opacity=".08"/>${S.demoStep===4?'<text x="746" y="94" text-anchor="end" fill="#799788" font-size="11" font-family="monospace">3.14159265…</text>':''}`;
  }
  const points=Array.from({length:81},(_,i)=>{const x=i/80;return [30+x*740,148-(4/(1+x*x))*28];});
  const path=points.map(([x,y],i)=>`${i?'L':'M'}${x.toFixed(2)} ${y.toFixed(2)}`).join('');
  const part=S.demoStep<2?0:S.demoStep>2?1:Math.min(1,.25+((performance.now()-S.demoOrigin)%8000)/10000);
  const filled=points.slice(0,Math.max(2,Math.floor(part*80)+1));
  const area=`M30 148${filled.map(([x,y])=>`L${x} ${y}`).join('')}L${filled.at(-1)[0]} 148Z`;
  const n=5+S.digits/5;
  let samples='';
  if(S.demoStep>=2)for(let i=1;i<n;i++){const x=i/n;if(x<=part)samples+=`<circle cx="${30+x*740}" cy="${148-(4/(1+x*x))*28}" r="2" fill="#9ab7bb"/>`;}
  return `<defs><linearGradient id="integralFill" x1="0" y1="0" x2="0" y2="1"><stop offset="0%" stop-color="#b1d1d0" stop-opacity=".4"/><stop offset="100%" stop-color="#b1d1d0" stop-opacity=".04"/></linearGradient></defs><path d="M30 148H770" stroke="#e5edee"/><path d="M30 82H770M30 115H770" stroke="#edf2f3" stroke-dasharray="2 7"/><path d="${area}" fill="url(#integralFill)"/><path d="${path}" fill="none" stroke="#adc5cb" stroke-width="1.7"/>${samples}<text x="30" y="163" fill="#b0bdc1" font-size="8" font-family="monospace">0</text><text x="768" y="163" fill="#b0bdc1" font-size="8" font-family="monospace">1</text>${S.demoStep===4?'<text x="700" y="126" text-anchor="end" font-family="serif" font-size="39" fill="#77a293">π</text>':''}`;
}
function renderChart(){
  const run=currentRun();
  if(isDemo()){$('mainChart').innerHTML=demoChart();$('chartLabel').textContent=S.demoStep>=3?'Enclosures · illustration':'4 / (1 + x²)';$('mainChart').setAttribute('aria-label',S.demoStep>=3?'Illustrative overlapping error enclosures from two routes. Increase target digits to narrow the drawn intervals. No values are calculated or certified.':'Illustrative quadrature on the function 4 divided by 1 plus x squared. The demo does not run or certify a calculation.');return;}
  if(run?.source==='imported'){
    const counts=Object.values(run.packages).reduce((a,v)=>(a[v]=(a[v]||0)+1,a),{});
    let start=30,html='<path d="M30 140H770" stroke="#e8eeef"/>';
    for(const [status,color] of [['passed','#9fcbb3'],['needs_data','#d7c096'],['failed','#cca7aa']]){const width=(counts[status]||0)/50*740;html+=`<rect x="${start}" y="77" height="15" width="${Math.max(0,width-3)}" rx="3" fill="${color}"/><text x="${start+width/2}" y="118" text-anchor="middle" fill="#97aab1" font-family="monospace" font-size="10">${counts[status]||0}</text>`;start+=width;}
    $('mainChart').innerHTML=html;$('chartLabel').textContent='Package checks · combined record';$('mainChart').setAttribute('aria-label','45 package checks passed, 3 required data, 2 failed in Linux-specific tests.');return;
  }
  const progress=run?.metrics?.completed;
  if(progress?.total){const ratio=Math.min(1,Math.max(0,progress.value/progress.total));$('mainChart').innerHTML=`<rect x="30" y="86" width="740" height="10" rx="5" fill="#eaf0ed"/><rect x="30" y="86" width="${ratio*740}" height="10" rx="5" fill="#97bba5"/><text x="770" y="133" text-anchor="end" fill="#8eaaa0" font-size="14" font-family="monospace">${progress.value} / ${progress.total}</text>`;$('chartLabel').textContent=`Reported progress · ${progress.unit||'items'}`;$('mainChart').setAttribute('aria-label',`${progress.value} of ${progress.total} ${progress.unit||'items'} reported complete`);return;}
  const samples=(run?.resources||[]).filter(r=>r.cpu!=null);
  if(samples.length<2){$('mainChart').innerHTML='<path d="M30 142H770" stroke="#e4ecee"/><text class="empty-state-text" x="400" y="104" text-anchor="middle">No resource samples</text>';$('chartLabel').textContent=run?'Activity':'—';return;}
  const max=Math.max(100,...samples.map(r=>r.cpu))*1.1;
  const points=samples.map((r,i)=>[30+i/Math.max(1,samples.length-1)*740,145-r.cpu/max*100]);
  const line=points.map(([x,y],i)=>`${i?'L':'M'}${x} ${y}`).join('');
  $('mainChart').innerHTML=`<defs><linearGradient id="cpuFill" x1="0" y1="0" x2="0" y2="1"><stop offset="0%" stop-color="#a7c4ba" stop-opacity=".4"/><stop offset="100%" stop-color="#a7c4ba" stop-opacity=".05"/></linearGradient></defs><path d="M30 145H770M30 94H770M30 43H770" stroke="#e6eeed" stroke-dasharray="2 6"/><path d="M30 145${line.slice(1)}L770 145Z" fill="url(#cpuFill)"/><path d="${line}" stroke="#8bb2a0" stroke-width="1.7" fill="none"/><text x="30" y="163" font-size="8" fill="#a0b1b8" font-family="monospace">${clock(samples[0].at)}</text><text x="770" y="163" text-anchor="end" font-size="8" fill="#a0b1b8" font-family="monospace">${clock(samples.at(-1).at)}</text>`;
  $('chartLabel').textContent='CPU · activity';$('mainChart').setAttribute('aria-label','Observed process CPU activity over time. This is activity, not output progress.');
}

function renderReadouts(){
  const run=currentRun();let values;
  if(isDemo())values=[['Input','0 → 1',''],['Target',S.digits,'digits'],['Method','Quadrature',''],['Form','π','']];
  else if(run?.source==='imported')values=[['Packages','50',''],['Passed','45',''],['Need data','3',''],['Platform','2','']];
  else{
    const resources=run?.resources||[],last=resources.at(-1)||{};
    const cpu=run?.status==='running'?last.cpu:run?.peak?.cpu;
    const memory=run?.status==='running'?last.memory_mb:run?.peak?.memory_mb;
    const progress=run?.metrics?.completed;
    values=[['Elapsed',run?duration((run.ended||S.snapshot.at)-run.started):'—',''],[run?.status==='running'?'CPU':'Peak CPU',cpu!=null&&cpu>=0?Math.round(cpu):'—',cpu!=null&&cpu>=0?'%':''],[run?.status==='running'?'Memory':'Peak memory',memory!=null&&memory>=0?Math.round(memory):'—',memory!=null&&memory>=0?'MB':''],[progress?'Progress':'Precision',progress?`${progress.value}${progress.total?'/'+progress.total:''}`:run?.metrics?.digits?.value??'—',progress?progress.unit||'':run?.metrics?.digits?'digits':'']];
  }
  $('readouts').innerHTML=values.map(([label,value,unit])=>`<div class="readout"><div class="readout-label">${esc(label)}</div><div class="readout-value">${esc(value)}${unit?`<small>${esc(unit)}</small>`:''}</div></div>`).join('');
}
function renderDemoControls(){
  $('demoControls').hidden=!isDemo();
  $('demoSteps').innerHTML=STAGES.map((s,i)=>`<button class="${i===S.demoStep?'active':''}" aria-label="${s.name}" title="${s.name}" data-demo-step="${i}"></button>`).join('');
  $('demoSteps').querySelectorAll('button').forEach(b=>b.onclick=()=>demoStep(Number(b.dataset.demoStep)));
  $('demoPlay').setAttribute('aria-label',S.demoPlaying?'Pause demonstration':'Play demonstration');
  $('demoPlay').innerHTML=`<svg viewBox="0 0 24 24"><path d="${S.demoPlaying?'M9 6v12m6-12v12':'M9 6l9 6-9 6Z'}"/></svg>`;
}
function renderGates(){
  const run=currentRun(),demo=isDemo();
  $('checkScope').textContent=demo?'Illustrative':Object.keys(run?.gates||{}).length?'Reported':run?.source==='imported'?'Result gates unreported':'Not reported';
  const gateHtml=GATES.map((g,i)=>{
    const state=demo?(S.demoStep>=3?'passed':'unreported'):run?.gates?.[g.id]?.state||'unreported';
    const symbol=state==='passed'?'M7 12l3 3 7-7':state==='failed'?'M8 8l8 8m-8 0 8-8':'M9 12h6';
    return `<button class="gate ${state}" data-gate="${i}" aria-label="${esc(g.name)}: ${state}"><svg viewBox="0 0 24 24"><circle class="gate-circle" cx="12" cy="12" r="10"/><path class="gate-symbol" d="${symbol}" fill="none" stroke-linecap="round" stroke-linejoin="round"/></svg><span>${esc(g.name)}</span></button>`;
  }).join('');
  if(DOM_CACHE.gates===gateHtml)return;DOM_CACHE.gates=gateHtml;$('gateGrid').innerHTML=gateHtml;
  $('gateGrid').querySelectorAll('button').forEach(b=>b.onclick=()=>explainGate(Number(b.dataset.gate)));
}
function renderPath(){
  const run=currentRun(),demo=isDemo();
  const tools=demo?DEMO_TOOLS:(run?.tools||[]).filter(t=>!run?.packages?.[t]);
  $('pathScope').textContent=demo?'Illustrative route':run?.source==='imported'?'50 package batteries':run?.source==='observed'?'Process only':'Observed';
  const list=tools.slice(0,7);
  const pathKey=JSON.stringify([list,run?.packages]);if(DOM_CACHE.path===pathKey)return;DOM_CACHE.path=pathKey;
  $('toolPath').innerHTML=list.length?list.map((id,i)=>{const tool=toolById(id);return `${demo&&i?'<span class="path-arrow">→</span>':''}<button class="tool-chip" data-tool="${esc(id)}" style="--chip-color:${esc(tool?.color||'#80918b')}"><i></i>${esc(tool?.name||id)}</button>`;}).join(''):(run?.packages&&Object.keys(run.packages).length?`<button class="text-button" id="packageDetailButton">${Object.keys(run.packages).length} recorded package checks ${arrowSvg}</button>`:'<span class="empty-path">No tool reported</span>');
  $('toolPath').querySelectorAll('[data-tool]').forEach(b=>b.onclick=()=>openTool(b.dataset.tool));
  $('packageDetailButton')?.addEventListener('click',openOutput);
}

function renderMap(){
  if(!S.catalog)return;
  const active=new Set(isDemo()?DEMO_TOOLS:currentRun()?.tools||[]),query=S.query.toLowerCase();
  const mapKey=JSON.stringify([S.layer,query,[...active].sort()]);
  if(DOM_CACHE.map===mapKey)return;DOM_CACHE.map=mapKey;
  let matched=0,html='';
  if(S.layer==='tools'){
    const centers=S.catalog.groups.map((g,i)=>({g,x:88+(i%3)*157,y:74+Math.floor(i/3)*127}));
    for(let i=0;i<centers.length;i++)for(const j of [i+1,i+3])if(j<centers.length&&(j===i+3||Math.floor(i/3)===Math.floor(j/3))){const a=centers[i],b=centers[j];html+=`<path class="group-link" d="M${a.x} ${a.y}L${b.x} ${b.y}"/>`;}
    for(const {g,x,y} of centers){
      const matching=g.tools.some(id=>{const t=toolById(id);return !query||`${t.name} ${t.id} ${t.meaning} ${g.name}`.toLowerCase().includes(query);});
      html+=`<g class="group-node ${matching?'':'dimmed'}" data-group="${g.id}" role="button" tabindex="0" aria-label="${esc(g.name)}. ${esc(g.meaning)}"><circle class="group-halo" cx="${x}" cy="${y}" r="38"/><circle class="group-core" cx="${x}" cy="${y}" r="22"/><text class="group-count" x="${x}" y="${y+3}" text-anchor="middle">${g.tools.length}</text><text x="${x}" y="${y+64}" text-anchor="middle">${esc(g.name)}</text></g>`;
      g.tools.forEach((id,i)=>{
        const t=toolById(id),angle=-Math.PI/2+i/g.tools.length*Math.PI*2,r=38;
        const tx=x+Math.cos(angle)*r,ty=y+Math.sin(angle)*r;
        const match=!query||`${t.name} ${t.id} ${t.meaning} ${g.name}`.toLowerCase().includes(query);
        if(match)matched++;
        html+=mapNode(t,tx,ty,active.has(id),!match);
      });
    }
  }else{
    const centers=[{x:139,y:178,r:92,n:7,label:'Method'},{x:357,y:178,r:78,n:5,label:'Review'}];
    for(let c=0;c<2;c++){
      const center=centers[c];html+=`<circle cx="${center.x}" cy="${center.y}" r="${center.r}" class="group-link"/><g class="group-node"><circle class="group-core" cx="${center.x}" cy="${center.y}" r="29"/><text x="${center.x}" y="${center.y+4}" text-anchor="middle">${center.label}</text></g>`;
      S.catalog.protocols.slice(c?7:0,c?12:7).forEach((t,i)=>{
        const angle=-Math.PI/2+i/center.n*2*Math.PI,x=center.x+Math.cos(angle)*center.r,y=center.y+Math.sin(angle)*center.r;
        const match=!query||`${t.id} ${t.name} ${t.meaning}`.toLowerCase().includes(query);if(match)matched++;
        html+=mapNode(t,x,y,false,!match)+`<text x="${x}" y="${y+21}" text-anchor="middle" fill="${match?'#96a3b1':'#d7dde3'}" font-family="inherit" font-size="9">${esc(t.name)}</text>`;
      });
    }
  }
  $('mapSvg').innerHTML=html;
  $('mapCount').textContent=query?`${matched} matches`:S.layer==='tools'?'50':'12';
  $('searchEmpty').hidden=matched!==0;
  $('toolSearch').placeholder=S.layer==='tools'?'Find a tool':'Find a protocol';
  $('mapSvg').querySelectorAll('[data-tool]').forEach(node=>{
    const tool=toolById(node.dataset.tool),action=()=>openTool(tool.id);
    node.addEventListener('click',action);
    node.addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();action();}});
    node.addEventListener('mouseenter',()=>mapTooltip(node,tool));
    node.addEventListener('focus',()=>mapTooltip(node,tool));
    node.addEventListener('mouseleave',()=>{$('mapTooltip').classList.remove('show');});
    node.addEventListener('blur',()=>{$('mapTooltip').classList.remove('show');});
  });
  $('mapSvg').querySelectorAll('[data-group]').forEach(node=>{const action=()=>openGroup(node.dataset.group);node.onclick=action;node.onkeydown=e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();action();}};});
  document.querySelectorAll('[data-layer]').forEach(b=>b.classList.toggle('active',b.dataset.layer===S.layer));
}
function mapNode(t,x,y,active,dimmed){return `<g class="map-node ${active?'active':''} ${dimmed?'dimmed':''}" data-tool="${esc(t.id)}" tabindex="0" role="button" aria-label="${esc(t.name)}. ${esc(t.meaning)}" transform="translate(${x},${y})" style="--node-color:${esc(t.color)}"><circle class="hit" r="14"/><circle class="tool-halo" r="10"/><circle class="dot" r="4"/><title>${esc(t.name)}</title></g>`;}
function mapTooltip(node,tool){const wrap=$('mapTooltip').parentElement.getBoundingClientRect(),rect=node.getBoundingClientRect();$('mapTooltip').innerHTML=`${esc(tool.name)}<small>${esc(tool.type==='protocol'?'Protocol':S.catalog.groups.find(g=>g.id===tool.group)?.name)}</small>`;$('mapTooltip').style.left=Math.max(65,Math.min(wrap.width-65,rect.x-wrap.x+rect.width/2))+'px';$('mapTooltip').style.top=(rect.y-wrap.y-5)+'px';$('mapTooltip').classList.add('show');}

function renderHistory(){
  const history=S.snapshot?.history||[];
  $('historyCount').textContent=history.length;
  $('historyExpand').textContent=S.historyExpanded?'Less':'All runs';
  const historyKey=JSON.stringify([history,S.selected,S.historyExpanded]);if(DOM_CACHE.history===historyKey)return;DOM_CACHE.history=historyKey;
  $('historyList').innerHTML=history.slice(0,S.historyExpanded?100:4).map(r=>{
    const tool=toolById(r.tool);
    const icon=r.status==='completed'?'M5 12l4 4L19 6':r.status==='running'?'M9 6v12m6-12v12':r.status==='failed'?'M6 6l12 12M6 18 18 6':'M5 7h14M5 12h14M5 17h9';
    return `<button class="history-row ${S.selected===r.id?'selected':''}" data-run="${esc(r.id)}" aria-label="${esc(r.title)}, ${esc(statusName(r.status))}"><span class="history-icon ${r.status}"><svg viewBox="0 0 24 24"><path d="${icon}"/></svg></span><span class="history-name">${esc(r.title)}<span class="history-source">${esc(r.source==='imported'?'Imported checks':r.source==='observed'?'Observed process':'Recorded run')}</span></span><span class="history-tool">${esc(tool?.name||(r.source==='imported'?'50 packages':r.engine||'Python'))}</span><span class="history-time">${esc(dateLabel(r.started))}</span><span class="history-status ${r.status}">${esc(statusName(r.status))}</span><span class="history-chevron">${arrowSvg}</span></button>`;
  }).join('');
  $('historyList').querySelectorAll('button').forEach(b=>b.onclick=()=>setMode('history',b.dataset.run));
}
function render(){
  if(!S.catalog)return;
  renderConnection();const run=currentRun(),demo=isDemo();
  $('runTitle').textContent=demo?'Certified integral':run?.title||'Loading run';
  $('runBadge').textContent=demo?'Demo':!S.online?'Last seen':run?.source==='imported'?'Imported':run?.source==='observed'?'Observed':run?.status==='running'?'Running':statusName(run?.status||'');
  $('runBadge').className='status-badge '+(demo?'demo':!S.online?'history':run?.status==='failed'?'failed':run?.status==='running'?'':'history');
  document.querySelectorAll('[data-mode]').forEach(b=>b.classList.toggle('active',b.dataset.mode===effectiveMode()));
  const liveButton=document.querySelector('.mode-switch [data-mode="auto"]');liveButton.textContent=S.snapshot?.active.length?`Live · ${S.snapshot.active.length}`:'Live';
  renderFlow();renderChart();renderReadouts();renderDemoControls();renderMap();renderGates();renderPath();renderHistory();
  if(window.renderProof)window.renderProof();
  $('outputButton').disabled=demo||!run;
}

function drawer(eyebrow,html){
  S.drawerFocus=document.activeElement;
  $('drawerEyebrow').textContent=eyebrow;$('drawerContent').innerHTML=html;$('drawer').hidden=false;$('drawerBackdrop').hidden=false;
  $('drawerClose').focus();
}
function closeDrawer(){$('drawer').hidden=true;$('drawerBackdrop').hidden=true;if(S.drawerFocus?.isConnected)S.drawerFocus.focus();else $('toolSearch').focus();}
function openGroup(id){const group=S.catalog.groups.find(g=>g.id===id);if(!group)return;drawer('CAPABILITY',`<h2 id="drawerTitle">${esc(group.name)}</h2><p>${esc(group.meaning)}</p><div class="drawer-callout">Grouped by purpose. These tools are choices, not a mandatory chain.</div>${group.tools.map(id=>`<div class="check-item"><button data-tool="${id}">${esc(toolById(id).name)}</button><span>↗</span></div>`).join('')}`);$('drawerContent').querySelectorAll('[data-tool]').forEach(b=>b.onclick=()=>openTool(b.dataset.tool));}
function openTool(id){
  const t=toolById(id);if(!t)return;
  const status=t.verification==='PASS'?'Battery passed':t.verification==='FAIL'?'Linux check failed':t.verification==='REFUSED (by design)'?'Needs reference data':'Installed';
  drawer(t.type==='protocol'?'PROTOCOL':'TOOL',`<h2 id="drawerTitle">${esc(t.name)}</h2><p>${esc(t.meaning)}</p><div class="drawer-diagram"><div class="diagram-end">${esc(t.input)}</div><span class="path-arrow">→</span><div class="diagram-middle">${t.type==='protocol'?'✓':'∿'}</div><span class="path-arrow">→</span><div class="diagram-end">${esc(t.output)}</div></div><div class="drawer-meta"><span>${t.type==='protocol'?'Available':'Installation check'}</span><strong>${esc(status)}</strong></div>${t.class?`<div class="drawer-meta"><span>Battery scope</span><strong>${esc(t.class)}</strong></div>`:''}${t.type==='tool'?'<div class="drawer-callout">A passing package battery can contain explicit engine skips. It does not accept a new scientific result.</div>':''}<details><summary>Source</summary>${t.source?`<div class="source-locator">${esc(t.source.path)}:${t.source.line}</div><blockquote>${esc(t.source.quote)}</blockquote>`:`<div class="source-locator">${esc(t.guide)}</div>`}</details><details id="guideDetails"><summary>Guide</summary><pre id="guideText">Loading…</pre></details>`);
  const terms=TERMS.filter(([word])=>t.meaning.toLowerCase().includes(word)).slice(0,3);
  if(terms.length){const details=document.createElement('details');details.innerHTML=`<summary>Terms</summary>${terms.map(([,name,meaning])=>`<div class="term-definition"><strong>${esc(name)}</strong><span>${esc(meaning)}</span></div>`).join('')}`;$('guideDetails').before(details);}
  let loaded=false;
  $('guideDetails').addEventListener('toggle',async()=>{if(!$('guideDetails')?.open||loaded)return;loaded=true;try{const response=await fetch('/api/guide/'+encodeURIComponent(id));if(!response.ok)throw new Error('Guide unavailable');const data=await response.json();if($('guideText'))$('guideText').textContent=data.text;}catch(error){if($('guideText'))$('guideText').textContent='Guide unavailable';}});
}
function explainStage(index){const stage=STAGES[index];drawer('FLOW',`<h2 id="drawerTitle">${stage.name}</h2><p>${esc(stage.meaning)}</p><div class="drawer-diagram"><div class="diagram-end">${esc(index===0?'Question':STAGES[index-1].name)}</div><span class="path-arrow">→</span><div class="diagram-middle">${index+1}</div><span class="path-arrow">→</span><div class="diagram-end">${esc(index===4?'Saved evidence':STAGES[index+1].name)}</div></div>${isDemo()?`<div class="drawer-callout">Demo: ${esc(stage.demo)} The route and check indicators are illustrative.</div>`:'<div class="drawer-callout">Only explicitly reported internal stages are shown as observed. The recorder can see a process start or end without knowing its internal scientific progress.</div>'}`);}
function explainGate(index){
  const gate=GATES[index],reported=currentRun()?.gates?.[gate.id];
  drawer('CHECK',`<h2 id="drawerTitle">${esc(gate.title)}</h2><p>${esc(gate.meaning)}</p><div class="drawer-meta"><span>State</span><strong>${esc(isDemo()?'Illustrative':reported?.state||'Not reported')}</strong></div>${reported?.detail?`<div class="drawer-callout">${esc(reported.detail)}</div>`:''}<div class="drawer-callout">${isDemo()?'The demo does not execute a computation. Green marks illustrate the role of the checks.':'A reported check records what the computation emitted. The dashboard does not independently certify the claim.'}</div><button class="text-button" id="gateProtocol">Read the protocol ${arrowSvg}</button>`);
  $('gateProtocol').onclick=()=>openTool(gate.id==='known_truth'?'planted-truth':gate.id==='independent'?'independence-bookkeeping':'acceptance-gate');
}
function openInstallation(){
  drawer('INSTALLATION',`<h2 id="drawerTitle">50 instruments</h2><div class="mini-bar"><span style="width:90%;background:#a8cbb5"></span><span style="width:6%;background:#d5c29e"></span><span style="width:4%;background:#cda8ad"></span></div><div class="installation-counts"><div><strong>45</strong><span>Passed</span></div><div><strong style="color:#b69b6e">3</strong><span>Need data</span></div><div><strong style="color:#b98b91">2</strong><span>Platform limits</span></div></div><p>The installation record combines package batteries from three runs. Scientific acceptance checks are separate.</p><div class="drawer-callout">AMFlow Kit and Seedling have failing Linux-specific process checks on this Mac. FFCapital, Frobenius, and Galois require reference data.</div><div class="source-locator">installation-validation.json</div><button id="viewInstallationRun" class="text-button">Open recorded checks ${arrowSvg}</button>`);
  $('viewInstallationRun').onclick=()=>{closeDrawer();setMode('history','installation');};
}
function openOutput(){
  const run=currentRun();if(!run)return;
  const output=run.events.filter(e=>e.type==='output');
  let body=`<h2 id="drawerTitle">${esc(run.title)}</h2><div class="drawer-meta"><span>Source</span><strong>${esc(run.source)}</strong></div>`;
  if(run.note)body+=`<p>${esc(run.note)}</p>`;
  if(run.command)body+=`<details><summary>Command</summary><pre>${esc(run.command.join(' '))}</pre></details>`;
  if(run.checks){body+=run.checks.map(c=>`<div class="check-item ${({PASS:'passed',FAIL:'failed','REFUSED (by design)':'needs_data'})[c.state]}"><button data-tool="${esc(c.tool)}">${esc(toolById(c.tool)?.name||c.tool)}</button><span>${esc(c.state==='REFUSED (by design)'?'Needs data':c.state)}</span></div>`).join('');}
  else body+=output.length?output.map(e=>`<div class="log-line"><span class="log-time">${clock(e.at)} · ${esc(e.stream)}</span>${esc(e.text)}</div>`).join(''):'<p>No output captured. A directly observed process provides activity only; the workspace launchers also capture output.</p>';
  if(run.artifacts?.length)body+=`<details><summary>Saved artifacts</summary><pre>${esc(run.artifacts.map(a=>a.path).join('\n'))}</pre></details>`;
  drawer('RECORD',body);$('drawerContent').querySelectorAll('[data-tool]').forEach(b=>b.onclick=()=>openTool(b.dataset.tool));
}
function openLearn(){
  drawer('WORKSPACE',`<h2 id="drawerTitle">Follow the work</h2><p>Flow shows the route. The map shows the instruments. Click a node or check to see its role.</p><div class="drawer-diagram"><div class="diagram-end">Question</div><span class="path-arrow">→</span><div class="diagram-middle">∿</div><span class="path-arrow">→</span><div class="diagram-end">Answer + checks</div></div><div class="drawer-meta"><span>Green</span><strong>Observed or reported</strong></div><div class="drawer-meta"><span>Gray</span><strong>Not reported</strong></div><div class="drawer-meta"><span>Demo</span><strong>Illustrative only</strong></div><div class="drawer-callout">CPU and memory show activity. Progress appears only when a job reports an actual completed-output count. No finish-time forecast is invented.</div><p>The map groups tools by purpose, not by mandatory dependencies. A real problem may use only a few.</p>`);
}
function openInfo(){
  drawer('LOCAL',`<h2 id="drawerTitle">This workspace</h2><div class="drawer-meta"><span>Connection</span><strong>${S.online?'Connected':'Disconnected'}</strong></div><div class="drawer-meta"><span>Refresh</span><strong>1 second</strong></div><div class="drawer-meta"><span>Scope</span><strong>bootscience</strong></div><p>Runs launched through the workspace commands are recorded automatically. Other Python and Julia processes in this workspace can be observed while the dashboard is open.</p><details><summary>Tracking</summary><pre>./bootloops-python your_script.py\n./bootloops-check mixalot eras\n\nOptional explicit telemetry:\nfrom telemetry import step, metric, gate</pre></details><details><summary>Operations</summary><p style="margin-top:17px">${esc(S.catalog.operations.meaning)}</p><div class="source-locator">${esc(S.catalog.operations.source)}</div></details><div class="drawer-callout">The interface is read-only. History stays in this workspace. Internal stages, numerical accuracy, and acceptance checks require explicit telemetry.</div>`);
}

function bind(){
  document.querySelectorAll('[data-mode]').forEach(b=>b.onclick=()=>setMode(b.dataset.mode));
  document.querySelectorAll('[data-layer]').forEach(b=>b.onclick=()=>{S.layer=b.dataset.layer;S.query='';$('toolSearch').value='';renderMap();});
  $('toolSearch').addEventListener('input',e=>{S.query=e.target.value;renderMap();});
  $('precision').addEventListener('input',e=>{S.digits=Number(e.target.value);$('precisionValue').textContent=S.digits;renderReadouts();renderChart();});
  $('demoPlay').onclick=()=>{if(!S.demoPlaying)S.demoOrigin=performance.now()-S.demoStep*8000;S.demoPlaying=!S.demoPlaying;renderDemoControls();};
  $('demoReset').onclick=()=>{S.demoStep=0;S.demoOrigin=performance.now();S.demoPlaying=true;render();};
  $('installationButton').onclick=openInstallation;
  $('historyExpand').onclick=()=>{S.historyExpanded=!S.historyExpanded;renderHistory();};
  $('flowHelp').onclick=()=>explainStage(isDemo()?S.demoStep:2);
  $('chartHelp').onclick=()=>drawer('PLOT',`<h2 id="drawerTitle">${isDemo()?'Numerical integration':currentRun()?.source==='imported'?'Package checks':'Activity and progress'}</h2><p>${isDemo()?'The area under this curve from 0 to 1 is π. Sampling the curve approximates the area. Certified arithmetic tracks a bound on the numerical error. The plot, sample marks, target digits, and checks are illustrative; no computation is running.':currentRun()?.source==='imported'?'Each segment counts package-battery outcomes. This is the combined installation record, not a scientific result.':'CPU counts the recorded process and its children, as a percentage of one core. Memory is their summed resident memory. Values can exceed 100% on multiple cores. Activity is not proof of output progress. Completed-output counts are shown only when explicitly reported.'}</p>`);
  $('learnButton').onclick=openLearn;$('infoButton').onclick=openInfo;$('outputButton').onclick=openOutput;
  $('drawerClose').onclick=closeDrawer;$('drawerBackdrop').onclick=closeDrawer;
  document.addEventListener('keydown',e=>{
    if(e.key==='Escape')closeDrawer();
    if(e.key==='Tab'&&!$('drawer').hidden){const items=[...$('drawer').querySelectorAll('button,a,input,summary,[tabindex="0"]')];const first=items[0],last=items.at(-1);if(e.shiftKey&&document.activeElement===first){e.preventDefault();last.focus();}else if(!e.shiftKey&&document.activeElement===last){e.preventDefault();first.focus();}}
  });
  $('reloadButton').onclick=()=>location.reload();
}
async function start(){
  bind();
  try{const response=await fetch('/api/catalog');if(!response.ok)throw new Error('Catalog unavailable');S.catalog=await response.json();$('installationBar').innerHTML='<span style="width:90%;background:#a8cbb5"></span><span style="width:6%;background:#d5c29e"></span><span style="width:4%;background:#cda8ad"></span>';render();connect();setInterval(advanceDemo,1000);}
  catch(error){console.error(error);$('startupError').hidden=false;}
}
start();
