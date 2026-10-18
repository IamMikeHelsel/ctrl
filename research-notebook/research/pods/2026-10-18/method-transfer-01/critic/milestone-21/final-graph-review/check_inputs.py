#!/usr/bin/env python3
"""Independent E11 binding, import, extraction and declaration inventory check.
Reads frozen originals and copied sources. Writes only this review directory.
"""
from pathlib import Path
import hashlib, json, re
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'lean-controls').is_dir())
COPY = HERE / 'builder-copy'
ORIGINAL = ROOT / 'research/pods/2026-10-18/method-transfer-01/erdos/final-graph-11'
EXPECTED = '64d2ab58dc3f2f0dd360d142f6a66bd2fd2b49fda288b50771d20b14508a8d76'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text())
def strip_comments(text):
    # Nested Lean block comments and line comments, preserving line positions.
    out=[]; i=0; depth=0
    while i<len(text):
        if text[i:i+2]=='/-': depth+=1; out.extend('  '); i+=2
        elif depth and text[i:i+2]=='-/': depth-=1; out.extend('  '); i+=2
        elif not depth and text[i:i+2]=='--':
            j=text.find('\n',i)
            if j<0:j=len(text)
            out.extend(' '*(j-i));i=j
        else:out.append('\n' if text[i]=='\n' else (' ' if depth else text[i]));i+=1
    assert depth==0
    return ''.join(out)

def main():
    manifest=read(ORIGINAL/'artifact-sha256.json')
    assert sha(ORIGINAL/'artifact-sha256.json')==sha(COPY/'artifact-sha256.json')==EXPECTED
    for rel,h in manifest['files'].items():
        assert sha(ORIGINAL/rel)==sha(COPY/rel)==h,rel
    inputs=read(COPY/'INPUTS.json'); prior=[]
    for item in inputs['prior_freezes']:
        p=ROOT/item['manifest']; assert sha(p)==item['sha256']
        entries=read(p)['files']
        for rel,h in entries.items():assert sha(p.parent/rel)==h,(p,rel)
        prior.append({'manifest':item['manifest'],'sha256':sha(p),'bindings':len(entries)})
    copies=[]
    for item in inputs['copies']:
        assert sha(COPY/item['copy'])==item['sha256'],item
        copies.append({**item,'original_current_match':sha(ROOT/item['original'])==item['sha256']})
    inherited=inputs['unchanged_inherited_modules']
    for mod,item in inherited.items():
        rel=Path(mod.replace('.','/')).with_suffix('.lean')
        assert sha(COPY/rel)==sha(ROOT/item['path'])==item['sha256']
    for item in inputs['unchanged_upstream_modules']:
        rel=Path(item['module'].replace('.','/')).with_suffix('.lean')
        assert sha(COPY/rel)==sha(ROOT/item['original'])==item['sha256']
    closure=read(COPY/'complete-closure.json'); imports={}; inventories={}; declarations=[]
    for mod,item in closure['modules'].items():
        p=COPY/item['source']; assert sha(p)==item['sha256']
        txt=strip_comments(p.read_text())
        imps=re.findall(r'^\s*import\s+([^\s]+)',txt,re.M)
        assert imps==item['imports'],mod
        imports[mod]=imps
        stack=[]; names=[]; private=[]
        for line in txt.splitlines():
            tokens=line.strip().split()
            if not tokens:continue
            if tokens[0]=='namespace':stack.append(tokens[1]);continue
            if tokens[0]=='end' and len(tokens)>1:
                assert stack and stack[-1]==tokens[1],(mod,line,stack)
                stack.pop();continue
            if tokens[0].startswith('@['):
                line=re.sub(r'^\s*@\[[^]]*\]\s*','',line);tokens=line.strip().split()
            is_private=bool(tokens and tokens[0]=='private')
            if is_private:tokens=tokens[1:]
            if tokens and tokens[0] in ('lemma','theorem'):
                name=tokens[1];assert re.fullmatch(r"[\w']+",name),(mod,name)
                full='.'.join(stack+[name]);(private if is_private else names).append(full)
        inventories[mod]={'public':names,'private_count':len(private),'source_sha256':sha(p)}
        declarations.extend(names)
        assert not re.search(r'\b(sorry|admit|native_decide|trustCompiler)\b|^\s*(axiom|unsafe)\b',txt,re.M),mod
    assert len(declarations)==len(set(declarations))==1966
    seen=set(); order=[]
    def visit(m):
        if m in seen:return
        assert m in imports,m
        seen.add(m)
        for dep in imports[m]:
            if dep=='Mathlib' or dep.startswith('Mathlib.'):continue
            visit(dep)
        order.append(m)
    visit('FinalControls')
    assert set(order)==set(closure['order']) and order==closure['order']
    assert len(order)==34
    assert not any(x in seen for x in ('Erdos128.LowDensityConstruction','PublishedBCL','FixedCutBound'))
    extracted=[]
    for dest,item in read(COPY/'extraction.json').items():
        text=(COPY/dest).read_bytes()
        for section in item['source_sections']:
            src=(COPY/section['file']).read_bytes().splitlines(keepends=True)
            raw=b''.join(src[section['start_line']-1:section['end_line']])
            assert hashlib.sha256(raw).hexdigest()==section['sha256']
            assert raw in text
            extracted.append(section)
    result={'checked_utc':datetime.now(timezone.utc).isoformat(),'passed':True,
      'builder_manifest_sha256':EXPECTED,'builder_original_and_copy_bindings':len(manifest['files']),
      'prior_freezes':prior,'prior_bindings':sum(x['bindings'] for x in prior),
      'input_copies':copies,'inherited_modules':len(inherited),'upstream_modules':len(inputs['unchanged_upstream_modules']),
      'complete_local_order':order,'public_declarations':len(declarations),
      'primed_public_names':sorted(n for n in declarations if "'" in n),
      'mechanical_CheckedTree_declarations':len(inventories['CheckedTree']['public']),
      'declaration_inventory':inventories,'extracted_exact_sections':extracted}
    (HERE/'input-check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('declaration_inventory','input_copies','prior_freezes','complete_local_order','extracted_exact_sections')},indent=2))
if __name__=='__main__':main()
