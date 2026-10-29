import {readFile,writeFile,mkdir,readdir} from 'node:fs/promises';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {spawnSync} from 'node:child_process';
import path from 'node:path';
import {Resvg} from '@resvg/resvg-js';
import {renderSketch,escapeXML as esc} from './src/sketch.mjs';
import {storiesFrom} from './stories.mjs';
const root=fileURLToPath(new URL('./',import.meta.url));
const repo=path.resolve(root,'../..');
const out=path.join(repo,'site/explainers/lab');
const report=JSON.parse(await readFile(path.join(out,'results.json'),'utf8'));
const source=await readFile(path.join(repo,'experiments/math_explainers/run.py'));
if(createHash('sha256').update(source).digest('hex')!==report.source_sha256)throw new Error('Experiment source changed. Run uv run experiments/math_explainers/run.py first.');
// Verify with the producer's canonical JSON convention (Python preserves 1.0).
const verify=spawnSync('uv',['run','--no-project','python','-c',"import json,hashlib,sys; p=json.load(open(sys.argv[1])); expected=p.pop('sha256'); actual=hashlib.sha256(json.dumps(p,sort_keys=True,separators=(',',':')).encode()).hexdigest(); sys.exit(0 if actual==expected else 1)",path.join(out,'results.json')],{encoding:'utf8'});
if(verify.status!==0)throw new Error('Experiment artifact checksum failed: '+(verify.stderr||''));
for(const id of ['lyapunov-energy','braking-budget','kalman-balance']){
 const meta=JSON.parse(await readFile(path.join(out,'exports',id,'story.json'),'utf8'));
 if(meta.source_derivation?.sha256!==report.sha256)throw new Error('Video is stale: '+id+'. Run uv run python tools/math_explainers/render.py.');
}
const stories=storiesFrom(report);
await mkdir(path.join(out,'exports'),{recursive:true});
const fontPath=path.join(root,'assets/Kalam-Regular.ttf');
const font=await readFile(fontPath);
const fontLicense=await readFile(path.join(root,'assets/Kalam-OFL.txt'),'utf8');
const fontCSS=`/* ${fontLicense.replaceAll('*/','* /')} */\n@font-face{font-family:Kalam;src:url(data:font/ttf;base64,${font.toString('base64')}) format('truetype');font-weight:400;font-style:normal;}`;
const css=await readFile(path.join(root,'web/player.css'),'utf8');
const js=await readFile(path.join(root,'web/player.js'),'utf8');
const safeJSON=value=>JSON.stringify(value).replace(/</g,'\\u003c').replace(/\u2028/g,'\\u2028').replace(/\u2029/g,'\\u2029');
const dataURI=async(file,type)=>`data:${type};base64,${(await readFile(path.join(out,file))).toString('base64')}`;
const head=(title,sketch=false)=>`<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><link rel="icon" href="data:,"><title>${esc(title)} · ctrl math explainers</title><style>${css}</style>${sketch?`<style id="font-face">${fontCSS}</style>`:''}</head>`;
function player(story) {
  const stage=story.kind==='video'?'<img id="poster" alt=""><video id="movie" muted playsinline preload="metadata" aria-label="Animated explanation" hidden></video>':story.steps.map((s,i)=>`<div class="frame" ${i?'hidden':''}>${s.svg}</div>`).join('');
  const payload={...story,steps:story.steps.map(({svg,exportSvg,...step})=>step)};
  return `${head(story.title,story.kind==='svg')}<body><main class="shell"><header class="header"><div><div class="eyebrow">${story.kind==='video'?'Manim · explanatory':'Rough.js · sketch'} / ${esc(story.category)}</div><h1>${esc(story.title)}</h1></div><a class="back" href="index.html">← Experiment gallery</a></header><section class="surface" aria-label="Diagram walkthrough"><div id="stage" class="stage">${stage}</div><div class="details" aria-live="polite" aria-atomic="true"><h2 id="step-title" class="step-title"></h2><p id="caption" class="caption"></p></div><div class="controls"><button id="previous" aria-label="Previous step">← Back</button><button id="next" aria-label="Next step">Next →</button><button id="replay">Replay step</button><span class="spacer"></span><button id="play" class="primary" aria-pressed="false">Play all</button><label class="speed">Speed <select id="speed"><option value="0.5">0.5×</option><option value="1" selected>1×</option><option value="1.5">1.5×</option><option value="2">2×</option></select></label></div><div class="timeline"><span id="count"></span><input id="seek" type="range" min="0" max="${story.steps.length-1}" value="0" step="1" aria-label="Walkthrough step"></div></section><nav class="chapters" aria-label="Steps">${story.steps.map((s,i)=>`<button data-step="${i}">${i+1}. ${esc(s.title.replace(/^\d+\. /,''))}</button>`).join('')}</nav><footer class="footer"><span class="kbd">← / → step · Space play / pause · Home / End</span><div class="downloads"><button id="save-png">Save step PNG</button>${story.kind==='video'?`<a href="${story.fullVideo}" download="${story.id}.mp4">Download MP4</a>`:'<button id="save-svg">Save step SVG</button>'}</div></footer><p id="status" class="status" role="status"></p></main><script type="application/json" id="story-data">${safeJSON(payload)}</script><script>${js}</script></body></html>`;
}
const catalog=[];
for(const source of stories) {
  const dir=path.join(out,'exports',source.id);await mkdir(dir,{recursive:true});
  const compiled={...source,kind:'svg',steps:[]};delete compiled.items;
  for(let i=0;i<source.steps.length;i++) {
    const svg=renderSketch(source,i,{fontCSS});
    const file=`step-${String(i+1).padStart(2,'0')}`;
    await writeFile(path.join(dir,file+'.svg'),svg);
    const png=new Resvg(svg,{font:{fontFiles:[fontPath],loadSystemFonts:false,defaultFontFamily:'Kalam'},fitTo:{mode:'width',value:2240}}).render().asPng();
    await writeFile(path.join(dir,file+'.png'),png);
    compiled.steps.push({...source.steps[i],svg:renderSketch(source,i)});
  }
  await writeFile(path.join(dir,'source.json'),JSON.stringify(source,null,2));
  await writeFile(path.join(out,source.id+'.html'),player(compiled));
  catalog.push({...source,kind:'svg',thumbnail:`exports/${source.id}/step-${String(source.steps.length).padStart(2,'0')}.png`});
}
for(const folder of (await readdir(path.join(out,'exports'))).sort()) {
  let source;try{source=JSON.parse(await readFile(path.join(out,'exports',folder,'story.json'),'utf8'));}catch(e){if(e.code==='ENOENT')continue;throw e;}
  const compiled={...source,steps:[],fullVideo:await dataURI(`exports/${source.id}/complete.mp4`,'video/mp4')};
  for(const step of source.steps)compiled.steps.push({...step,video:await dataURI(step.video,'video/mp4'),poster:await dataURI(step.poster,'image/png')});
  await writeFile(path.join(out,source.id+'.html'),player(compiled));
  catalog.push({...source,thumbnail:source.steps.at(-1).poster});
}
const sourceMap=Object.fromEntries(report.sources.map(s=>[s.id,s]));
const playerFor={lyapunov:'lyapunov-energy',braking:'braking-budget',kalman:'kalman-balance',saturation:'saturation-order',sumsets:'reachable-holes',scheduling:'schedule-bound'};
const visualCards=catalog.map(story=>`<a class="lab-card" href="${story.id}.html"><img src="${story.thumbnail}" width="1120" height="620" alt="${esc(story.title)}" loading="lazy"><span class="label">${story.kind==='video'?'Manim':'Rough.js'} · ${story.steps.length} steps</span><h3>${esc(story.title)}</h3><p>${esc(story.summary)}</p></a>`).join('');
const experimentCards=report.experiments.map((e,i)=>{
 const facts=e.witness??e.example??e.negative_control??{first:e.rows?.[0],last:e.rows?.at(-1)};
 return `<article class="experiment" id="${e.id}"><span class="label">${String(i+1).padStart(2,'0')} / ${esc(e.evidence)}</span><h2>${esc(e.title)}</h2><p class="question">${esc(e.question)}</p><p class="finding">${esc(e.conclusion)}</p><p class="small">${e.cases.toLocaleString('en-US')} declared cases. <a href="results.json">Raw results and exact inputs</a></p>${playerFor[e.id]?`<p><a class="launch" href="${playerFor[e.id]}.html">Walk through this result →</a></p>`:''}<details><summary>Inspect the ${e.witness?'witness':'worked values'}</summary><pre>${esc(JSON.stringify(facts,null,2))}</pre></details><dl><dt>What this establishes</dt><dd>${esc(e.scope)}</dd><dt>Next discriminating experiment</dt><dd>${esc(e.next_test)}</dd><dt>Reject the route if</dt><dd>${esc(e.kill_criterion)}</dd></dl><p class="sources">Source connections: ${e.source_ids.map(id=>`<a href="${esc(sourceMap[id].url)}">${esc(sourceMap[id].title)}</a>`).join(' · ')}</p></article>`;
}).join('');
const sourceCards=report.sources.map(s=>`<article><h3><a href="${esc(s.url)}">${esc(s.title)}</a></h3><p>${esc(s.use)}</p>${s.commit?`<p class="small">Pinned revision: <code>${s.commit}</code></p>`:''}${s.model_url?`<a href="${esc(s.model_url)}">Exact model definitions</a>`:''}</article>`).join('');
const nav=report.experiments.map((e,i)=>`<a href="#${e.id}">${i+1}. ${esc(e.title)}</a>`).join('');
const replacements={cards:visualCards,experiments:experimentCards,sources:sourceCards,nav,cases:report.experiments.reduce((n,e)=>n+e.cases,0).toLocaleString('en-US')};
let page=await readFile(path.join(root,'web/gallery.html'),'utf8');
page=page.replace(/\{\{(\w+)\}\}/g,(_,key)=>{if(!(key in replacements))throw new Error('Unknown template slot: '+key);return replacements[key];});
await writeFile(path.join(out,'index.html'),page);
await writeFile(path.join(out,'lab.css'),await readFile(path.join(root,'web/lab.css')));
await writeFile(path.join(out,'catalog.json'),JSON.stringify(catalog.map(({id,title,kind,steps})=>({id,title,kind,steps:steps.length,source_sha256:report.sha256})),null,2)+'\n');
async function inventory(dir){let files=[];for(const entry of await readdir(dir,{withFileTypes:true})){const absolute=path.join(dir,entry.name);if(entry.isDirectory())files.push(...await inventory(absolute));else if(entry.name!=='manifest.json'){const bytes=await readFile(absolute);files.push({path:path.relative(out,absolute),bytes:bytes.length,sha256:createHash('sha256').update(bytes).digest('hex')});}}return files.sort((a,b)=>a.path.localeCompare(b.path));}
await writeFile(path.join(out,'manifest.json'),JSON.stringify({schema_version:1,result_sha256:report.sha256,files:await inventory(out)},null,2)+'\n');
console.log(`Built ${catalog.length} walkthroughs and ${report.experiments.length} experiment cards.`);
