import rough from 'roughjs/bundled/rough.cjs.js';

export const palette = { ink: '#26332f', muted: '#66736b', paper: '#fffdf7', green: '#31775d', blue: '#356d97', orange: '#ad6028', yellow: '#f7e3a2' };
export const escapeXML = value => String(value).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&apos;'}[c]));
export function seedOf(value) {
  let hash = 2166136261;
  for (const c of String(value)) hash = Math.imul(hash ^ c.charCodeAt(0), 16777619);
  return (hash >>> 0) % 2147483646 + 1;
}
export function validateStory(story) {
  if (!/^[a-z0-9]+(?:-[a-z0-9]+)*$/.test(story.id)) throw new Error('Story id must be a lowercase slug');
  if (!story.title || !Array.isArray(story.steps) || !story.steps.length) throw new Error('A story needs a title and steps');
  const ids = new Set();
  for (const item of story.items ?? []) {
    if (!item.id || ids.has(item.id)) throw new Error(`Duplicate or missing item id: ${item.id}`);
    ids.add(item.id);
    if (!['box','ellipse','label','arrow','line','note','group'].includes(item.type)) throw new Error(`Unknown item type: ${item.type}`);
  }
  for (const step of story.steps) {
    if (!step.title || !Number.isFinite(step.durationMs) || step.durationMs < 250) throw new Error('Steps need a title and durationMs >= 250');
    if (!Array.isArray(step.show)) throw new Error('Each sketch step needs an explicit show list');
    for (const id of [...step.show, ...(step.focus ?? [])]) if (!ids.has(id)) throw new Error(`Unknown item id: ${id}`);
    for (const id of step.focus ?? []) if (!step.show.includes(id)) throw new Error(`Focused item must be shown: ${id}`);
  }
  return story;
}
export function renderSketch(story, stepIndex, { fontCSS = '' } = {}) {
  validateStory(story);
  if (!Number.isInteger(stepIndex) || !story.steps[stepIndex]) throw new Error('Step index is out of range');
  const g = rough.generator(), s = story.steps[stepIndex];
  const w = story.width ?? 1120, h = story.height ?? 620;
  const draw = shape => g.toPaths(shape).map(p => `<path d="${escapeXML(p.d)}" stroke="${escapeXML(p.stroke)}" stroke-width="${p.strokeWidth}" fill="${escapeXML(p.fill || 'none')}" stroke-linecap="round" stroke-linejoin="round"/>`).join('');
  const text = (str, x, y, size = 25, color = palette.ink, anchor = 'middle') => `<text x="${x}" y="${y}" font-family="Kalam, sans-serif" font-size="${size}" fill="${color}" text-anchor="${anchor}">${String(str).split('\n').map((line,i) => `<tspan x="${x}" dy="${i ? size * 1.35 : 0}">${escapeXML(line)}</tspan>`).join('')}</text>`;
  const fragments = story.items.filter(i => s.show.includes(i.id)).map(i => {
    const color = palette[i.color] ?? i.color ?? palette.ink;
    const opts = { seed: seedOf(`${story.seed ?? 144}:${i.id}`), roughness: story.roughness ?? 1.15, bowing: .8, stroke: color, strokeWidth: 1.9, fill: i.fill ? (palette[i.fill] ?? i.fill) : undefined, fillStyle: i.fillStyle ?? 'hachure', hachureGap: 9, fillWeight: .7 };
    let markup = '';
    if (['box','group','note'].includes(i.type)) {
      const fill = i.type === 'note' ? palette.yellow : opts.fill;
      markup = draw(g.rectangle(i.x,i.y,i.w,i.h,{...opts,fill,fillStyle:i.type === 'note' ? 'solid' : opts.fillStyle}));
      if (i.label) markup += text(i.label, i.x+i.w/2, i.y+i.h/2 - ((i.label.split('\n').length-1)*16) + 8, i.fontSize ?? 25);
    } else if (i.type === 'ellipse') {
      markup = draw(g.ellipse(i.x+i.w/2,i.y+i.h/2,i.w,i.h,opts));
      if (i.label) markup += text(i.label,i.x+i.w/2,i.y+i.h/2+8,i.fontSize??25);
    } else if (i.type === 'label') {
      markup = text(i.label,i.x,i.y,i.fontSize??25,color,i.anchor??'middle');
    } else if (i.type === 'line' || i.type === 'arrow') {
      const points = i.points;
      if (!points || points.length < 2 || points.some(p=>p.length !== 2 || p.some(v=>!Number.isFinite(v)))) throw new Error(`Invalid points: ${i.id}`);
      markup = draw(g.linearPath(points,opts));
      if (i.type === 'arrow') {
        const [a,b] = points.slice(-2), angle = Math.atan2(b[1]-a[1],b[0]-a[0]), len = 13;
        markup += draw(g.linearPath([[b[0]-len*Math.cos(angle-.45),b[1]-len*Math.sin(angle-.45)],b,[b[0]-len*Math.cos(angle+.45),b[1]-len*Math.sin(angle+.45)]],{...opts,seed:opts.seed+1}));
      }
      if (i.label) markup += text(i.label,i.labelX??(points[0][0]+points.at(-1)[0])/2,i.labelY??(points[0][1]+points.at(-1)[1])/2-16,i.fontSize??22,color);
    }
    const dim = s.focus?.length && !s.focus.includes(i.id) ? .47 : 1;
    return `<g data-item="${escapeXML(i.id)}" opacity="${dim}">${markup}</g>`;
  }).join('');
  const xmlCSS = fontCSS.replaceAll('&','&amp;').replaceAll('<','&lt;');
  return `<svg xmlns="http://www.w3.org/2000/svg" width="${w}" height="${h}" viewBox="0 0 ${w} ${h}" role="img" aria-label="${escapeXML(story.title+' — '+s.title)}"><title>${escapeXML(story.title+' — '+s.title)}</title><desc>${escapeXML(s.caption ?? '')}</desc><style>${xmlCSS}</style><rect width="${w}" height="${h}" fill="${palette.paper}"/>${text(story.title,54,60,31,palette.ink,'start')}${text(`${stepIndex+1} / ${story.steps.length}`,w-54,58,21,palette.muted,'end')}<path d="M54 82 H${w-54}" stroke="#dddcd3"/>${fragments}</svg>`;
}
