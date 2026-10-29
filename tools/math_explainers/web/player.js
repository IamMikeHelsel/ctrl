/* The player is renderer-independent: explicit states, input or timed traversal. */
(() => {
  'use strict';
  const story = JSON.parse(document.getElementById('story-data').textContent);
  const $ = id => document.getElementById(id);
  const video = $('movie'), poster = $('poster'), stage = $('stage');
  const reduced = matchMedia('(prefers-reduced-motion: reduce)');
  const params = new URLSearchParams(location.search);
  if (params.get('embed') === '1') document.documentElement.classList.add('embed');
  let index = 0, playing = false, completed = false, speed = 1, timer = null, started = 0;
  let remaining = story.steps[0].durationMs, generation = 0;
  const frames = [...document.querySelectorAll('.frame')];
  const chapters = [...document.querySelectorAll('[data-step]')];
  const active = () => playing || Boolean(video && !video.paused && !video.ended);
  const state = () => ({index, count:story.steps.length, playing, completed, speed, kind:story.kind});
  const emit = name => window.dispatchEvent(new CustomEvent(`diagram:${name}`,{detail:state()}));
  function clearClock() { if(timer !== null){clearTimeout(timer);timer=null;remaining=Math.max(0,remaining-(performance.now()-started)*speed);} }
  function sync() {
    const step = story.steps[index];
    $('step-title').textContent = step.title;
    $('caption').textContent = step.caption ?? '';
    $('count').textContent = `${index+1} / ${story.steps.length}`;
    $('seek').value = index;
    $('seek').setAttribute('aria-valuetext',`Step ${index+1}: ${step.title}`);
    $('previous').disabled = index === 0;
    $('next').disabled = index === story.steps.length-1;
    $('play').textContent = active() ? 'Pause' : (completed ? 'Play from start' : 'Play all');
    $('play').setAttribute('aria-pressed',String(active()));
    chapters.forEach((b,i)=>b.setAttribute('aria-current',i===index?'step':'false'));
    chapters.forEach((b,i)=>b.setAttribute('aria-pressed',String(i===index)));
  }
  function advanceTimed() {
    if (!playing) return;
    if(index < story.steps.length-1) show(index+1,{animate:true,continuePlaying:true});
    else {pause();completed=true;sync();emit('end');}
  }
  function schedule() {
    clearClock();
    started = performance.now();
    timer = setTimeout(()=>{timer=null;remaining=0;advanceTimed();},remaining/speed);
  }
  function playVideo() {
    const currentGeneration = generation;
    video.hidden=false;poster.hidden=true;video.playbackRate=speed;
    const promise = video.play();
    if(promise) promise.catch(error=>{
      if(currentGeneration!==generation || error.name==='AbortError') return;
      pause();video.hidden=true;poster.hidden=false;
      $('status').textContent='Playback could not start. Use Replay step to try again.';
    });
  }
  function pause() {
    clearClock();playing=false;
    if(video) video.pause();
    sync();emit('pause');
  }
  function show(next,{animate=false,continuePlaying=false}={}) {
    if(!Number.isInteger(next)||next<0||next>=story.steps.length) throw new RangeError('Step index is out of range');
    clearClock();generation++;if(video)video.pause();
    playing=continuePlaying;index=next;remaining=story.steps[index].durationMs;
    completed=index===story.steps.length-1&&!continuePlaying&&(!video||!animate||reduced.matches);
    $('status').textContent='';
    frames.forEach((frame,i)=>{frame.hidden=i!==index;frame.classList.toggle('enter',i===index&&animate&&!reduced.matches);});
    if(video) {
      poster.src=story.steps[index].poster;poster.alt=`${story.title}: ${story.steps[index].title}`;
      video.src=story.steps[index].video;video.poster=story.steps[index].poster;
      video.hidden=true;poster.hidden=false;video.load();
      if(animate&&!reduced.matches)playVideo();
      else if(playing)schedule();
    } else if(playing)schedule();
    sync();emit('stepchange');
  }
  function play() {
    if(playing)return;
    if(completed)show(0);
    playing=true;sync();
    if(video&&!reduced.matches) {
      if(video.ended)video.currentTime=0;
      playVideo();
    } else schedule();
    emit('play');
  }
  function setSpeed(value) {
    if(![.5,1,1.5,2].includes(value))throw new RangeError('Unsupported speed');
    clearClock();speed=value;$('speed').value=String(speed);
    if(video)video.playbackRate=speed;
    if(playing&&(!video||reduced.matches))schedule();
  }
  $('previous').addEventListener('click',()=>show(index-1,{animate:true}));
  $('next').addEventListener('click',()=>show(index+1,{animate:true}));
  $('replay').addEventListener('click',()=>show(index,{animate:true}));
  $('play').addEventListener('click',()=>active()?pause():play());
  $('seek').addEventListener('input',e=>show(Number(e.target.value)));
  $('speed').addEventListener('change',e=>setSpeed(Number(e.target.value)));
  chapters.forEach(b=>b.addEventListener('click',()=>show(Number(b.dataset.step),{animate:true})));
  if(video) {
    video.addEventListener('play',sync);
    video.addEventListener('pause',sync);
    video.addEventListener('ended',()=>{if(playing)advanceTimed();else{video.hidden=true;poster.hidden=false;completed=index===story.steps.length-1;sync();}});
    video.addEventListener('error',()=>{pause();video.hidden=true;poster.hidden=false;$('status').textContent='This browser could not load the video. Download the MP4 or try another browser.';});
  }
  document.addEventListener('keydown',event=>{
    if(event.altKey||event.ctrlKey||event.metaKey||event.target.closest('input,select,textarea,[contenteditable=true]'))return;
    if(event.code==='Space'&&event.target.closest('button,a'))return;
    if(event.key==='ArrowRight'){event.preventDefault();if(index<story.steps.length-1)show(index+1,{animate:true});}
    if(event.key==='ArrowLeft'){event.preventDefault();if(index>0)show(index-1,{animate:true});}
    if(event.code==='Space'){event.preventDefault();active()?pause():play();}
    if(event.key==='Home'){event.preventDefault();show(0);}
    if(event.key==='End'){event.preventDefault();show(story.steps.length-1);}
  });
  document.addEventListener('visibilitychange',()=>{if(document.hidden)pause();});
  reduced.addEventListener('change',()=>{pause();show(index);});
  function download(blob,name) {
    const url=URL.createObjectURL(blob),a=document.createElement('a');a.href=url;a.download=name;a.click();setTimeout(()=>URL.revokeObjectURL(url),3000);
  }
  function svgMarkup() {
    const svg=frames[index].querySelector('svg').cloneNode(true);
    svg.querySelector('style').textContent=$('font-face').textContent;
    return new XMLSerializer().serializeToString(svg);
  }
  $('save-png').addEventListener('click',async()=>{
    try {
      const image=new Image();
      image.src=video?story.steps[index].poster:'data:image/svg+xml;charset=utf-8,'+encodeURIComponent(svgMarkup());
      await image.decode();
      const canvas=document.createElement('canvas');canvas.width=image.naturalWidth*2;canvas.height=image.naturalHeight*2;
      canvas.getContext('2d').drawImage(image,0,0,canvas.width,canvas.height);
      const blob=await new Promise(resolve=>canvas.toBlob(resolve,'image/png'));
      if(!blob)throw new Error('No image');
      download(blob,`${story.id}-step-${index+1}.png`);
    }catch{$('status').textContent='PNG export failed. Use the ready-made PNG files in exports.';}
  });
  if($('save-svg'))$('save-svg').addEventListener('click',()=>download(new Blob([svgMarkup()],{type:'image/svg+xml'}),`${story.id}-step-${index+1}.svg`));
  window.diagramPlayer=Object.freeze({goTo:i=>show(i),next:()=>{if(index<story.steps.length-1)show(index+1,{animate:true});},previous:()=>{if(index>0)show(index-1,{animate:true});},play,pause,setSpeed,getState:state});
  show(0);
})();
