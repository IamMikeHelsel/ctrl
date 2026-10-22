"""Extract open JSP problem-bank entries. Usage: jsp_open.py <problems_dir> <out.json>"""
import re, glob, json, html, sys
src, out = sys.argv[1:3]
rows = []
for f in sorted(glob.glob(f'{src}/catalog-*.md')):
    for blk in re.split(r'<a id="JSP-', open(f).read())[1:]:
        jid = 'JSP-' + blk[:6]
        def fld(name):
            m = re.search(r'\| ' + name + r' \| (.*?) \|\n', blk)
            return html.unescape(re.sub(r'<br>', ' ', m.group(1))).strip() if m else ''
        st = fld('Current status')
        if not st.startswith('Open'): continue
        title = re.search(r'## JSP-\d+ · (.*)', blk)
        rows.append(dict(id=jid, title=title.group(1) if title else '', area=fld('Mathematical area'),
            description=fld('Problem description'), bounty=fld('Historical bounty'),
            erdos_keys=re.findall(r'\[(Er[A-Za-z]*\d+[a-z]?)\]', html.unescape(fld('Publication details'))),
            mentions_erdos=bool(re.search('Erd(ő|o)s', html.unescape(blk))), file=f.split('/')[-1]))
json.dump(rows, open(out, 'w'), ensure_ascii=False, indent=1)
print(len(rows), 'open;', sum(r['mentions_erdos'] for r in rows), 'mention Erdős;', sum(bool(r['bounty']) for r in rows), 'with bounty')
