"""Build theorem explainer pages: site/explainers/<slug>/explainer.md -> index.html.

    uv run --no-project --with markdown-it-py --with pyyaml tools/explainer/build.py --all
    uv run --no-project --with markdown-it-py --with pyyaml tools/explainer/build.py SLUG --check

Math in $...$ / $$...$$ is converted to MathML at build time (KaTeX via node), so pages ship
no JavaScript. `## Heading {#id}` sets section ids. `<!-- include: file.svg -->` inlines a
file from the explainer folder so SVG diagrams can follow the site theme.

--check runs the content rules from .claude/skills/theorem-explainer/SKILL.md and exits 1
on any error: required sections, Lean theorem names that really exist, media that exists,
alt text, and no em dashes.
"""

from __future__ import annotations

import argparse
import html
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

import yaml
from markdown_it import MarkdownIt

ROOT = Path(__file__).resolve().parents[2]
TOOLS = Path(__file__).resolve().parent
SITE = ROOT / "site"
EXPLAINERS = SITE / "explainers"
REPO_URL = "https://github.com/IamMikeHelsel/ctrl/blob/main"

REQUIRED_SECTIONS = ["idea", "statement", "why", "simple", "harder", "applies", "limits", "check"]
REQUIRED_META = ["title", "subtitle", "slug", "lean", "theorems", "updated"]
# Hype and talking-down words. Warnings, not errors: occasionally one is the right word.
SOFT_BANNED = [
    "obviously",
    "clearly",
    "trivially",
    "simply",
    "just",
    "easy",
    "easily",
    "of course",
    "powerful",
    "elegant",
    "beautiful",
    "remarkable",
    "stunning",
    "revolutionary",
    "groundbreaking",
    "game-changing",
    "magic",
    "it is well known",
    "as everyone knows",
]
HARD_BANNED_CHARS = {"\u2014": "em dash"}


@dataclass
class Report:
    errors: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)

    def err(self, msg: str) -> None:
        self.errors.append(msg)

    def warn(self, msg: str) -> None:
        self.warnings.append(msg)


# ---------------------------------------------------------------- parsing helpers


def split_front_matter(text: str) -> tuple[dict, str]:
    m = re.match(r"^---\n(.*?)\n---\n(.*)$", text, re.S)
    if not m:
        raise SystemExit("explainer.md must start with YAML front matter between --- lines")
    return yaml.safe_load(m.group(1)) or {}, m.group(2)


CODE_RE = re.compile(r"(```.*?```|`[^`\n]+`)", re.S)
DISPLAY_RE = re.compile(r"\$\$(.+?)\$\$", re.S)
INLINE_RE = re.compile(r"(?<![\\$])\$(?!\s)([^$\n]+?)(?<!\s)\$(?!\$)")


def extract_math(body: str) -> tuple[str, list[dict]]:
    """Replace math with placeholders, leaving code spans and fences untouched."""
    items: list[dict] = []

    def stash(tex: str, display: bool) -> str:
        items.append({"tex": tex.strip(), "display": display})
        return f"MATHPH{len(items) - 1}X"

    out = []
    for i, chunk in enumerate(CODE_RE.split(body)):
        if i % 2 == 1:  # code
            out.append(chunk)
            continue
        chunk = DISPLAY_RE.sub(lambda m: "\n\n" + stash(m.group(1), True) + "\n\n", chunk)
        chunk = INLINE_RE.sub(lambda m: stash(m.group(1), False), chunk)
        out.append(chunk)
    return "".join(out), items


def render_math(items: list[dict], rep: Report) -> list[str]:
    if not items:
        return []
    if not (TOOLS / "node_modules" / "katex").exists():
        subprocess.run(["npm", "install", "--silent"], cwd=TOOLS, check=True)
    res = subprocess.run(
        ["node", str(TOOLS / "render_math.mjs")],
        input=json.dumps(items),
        capture_output=True,
        text=True,
        check=True,
    )
    data = json.loads(res.stdout)
    for e in data["errors"]:
        rep.err(f"math #{e['i']} `{e['tex']}`: {e['message']}")
    return data["ok"]


HEADING_RE = re.compile(r"^(#{2,3})[ \t]+(.+?)[ \t]*\{#([a-z0-9-]+)\}[ \t]*$", re.M)
INCLUDE_RE = re.compile(r"<!--\s*include:\s*([\w./-]+)\s*-->")


def lean_line(lean_path: Path, name: str) -> int | None:
    pat = re.compile(rf"^\s*(?:private\s+)?(?:theorem|lemma|def)\s+{re.escape(name)}\b")
    for n, line in enumerate(lean_path.read_text().splitlines(), 1):
        if pat.match(line):
            return n
    return None


# ---------------------------------------------------------------- checks


def check_source(meta: dict, body: str, folder: Path, rep: Report) -> None:
    for k in REQUIRED_META:
        if k not in meta:
            rep.err(f"front matter is missing `{k}`")
    full = yaml.safe_dump(meta) + body
    for ch, name in HARD_BANNED_CHARS.items():
        for n, line in enumerate(full.splitlines(), 1):
            if ch in line:
                rep.err(f"{name} on line {n}: {line.strip()[:70]}")
    prose = CODE_RE.sub("", body)
    prose = DISPLAY_RE.sub("", prose)
    prose = INLINE_RE.sub("", prose)
    for w in SOFT_BANNED:
        hits = re.findall(rf"\b{re.escape(w)}\b", prose, re.I)
        if hits:
            rep.warn(f"tone: '{w}' appears {len(hits)}x")
    ids = [m.group(3) for m in HEADING_RE.finditer(body)]
    for sec in REQUIRED_SECTIONS:
        if sec not in ids:
            rep.err(f"missing section `## ... {{#{sec}}}`")
    lean = ROOT / meta.get("lean", "")
    if not lean.is_file():
        rep.err(f"lean file not found: {meta.get('lean')}")
    else:
        for t in meta.get("theorems", []):
            if lean_line(lean, t) is None:
                rep.err(f"theorem `{t}` not found in {meta['lean']}")
    for m in re.finditer(r'(?:src|poster|href)="([^"#:]+)"', body):
        ref = m.group(1)
        if ref.startswith(("http", "/", "mailto")):
            continue
        if not (folder / ref).exists():
            rep.err(f"referenced file missing: {ref}")
    for m in INCLUDE_RE.finditer(body):
        if not (folder / m.group(1)).exists():
            rep.err(f"include missing: {m.group(1)}")
    for m in re.finditer(r"<img\b[^>]*>", body):
        if 'alt="' not in m.group(0):
            rep.err(f"<img> without alt: {m.group(0)[:60]}")
    for m in re.finditer(r"<video\b[^>]*>", body):
        tag = m.group(0)
        if "poster=" not in tag:
            rep.warn(f"<video> without poster: {tag[:60]}")
        if "aria-label=" not in tag:
            rep.err(f"<video> without aria-label: {tag[:60]}")


# ---------------------------------------------------------------- build


def build_one(folder: Path, check_only: bool) -> Report:
    rep = Report()
    src = folder / "explainer.md"
    meta, body = split_front_matter(src.read_text())
    check_source(meta, body, folder, rep)
    if check_only:
        render_math(extract_math(body)[1], rep)  # surface TeX errors too
        return rep
    if rep.errors:
        return rep

    body = INCLUDE_RE.sub(lambda m: (folder / m.group(1)).read_text(), body)
    toc = []

    def heading(m: re.Match) -> str:
        level, text, hid = len(m.group(1)), m.group(2), m.group(3)
        if level == 2:
            toc.append((hid, text))
        return f'<h{level} id="{hid}">{text}</h{level}>'

    body = HEADING_RE.sub(heading, body)
    body, math_items = extract_math(body)
    rendered = render_math(math_items, rep)
    if rep.errors:
        return rep

    rendered = [tidy_mathml(h) for h in rendered]
    md = MarkdownIt("commonmark", {"html": True, "typographer": False}).enable("table")
    out = md.render(body)
    for i, h in enumerate(rendered):
        # A display formula sits alone in its own paragraph.
        out = out.replace(f"<p>MATHPH{i}X</p>", f'<div class="math-display">{h}</div>')
        out = out.replace(f"MATHPH{i}X", h)

    lean_rel = meta["lean"]
    lean = ROOT / lean_rel
    links = []
    for t in meta["theorems"]:
        n = lean_line(lean, t)
        links.append(
            f'<li><a href="{REPO_URL}/{lean_rel}#L{n}"><code>{html.escape(t)}</code></a></li>'
        )
    nav = "".join(f'<a href="#{i}">{html.escape(strip_tags(t))}</a>' for i, t in toc)

    page = (TOOLS / "template.html").read_text()
    subs = {
        "{{title}}": html.escape(meta["title"]),
        "{{subtitle}}": html.escape(meta["subtitle"]),
        "{{eyebrow}}": html.escape(meta.get("eyebrow", "Theorem explainer")),
        "{{lean_file}}": f'<a href="{REPO_URL}/{lean_rel}"><code>{html.escape(lean_rel)}</code></a>',
        "{{theorem_links}}": "".join(links),
        "{{nav}}": nav,
        "{{body}}": out,
        "{{updated}}": html.escape(str(meta["updated"])),
    }
    for k, v in subs.items():
        page = page.replace(k, v)
    (folder / "index.html").write_text(page)
    return rep


def tidy_mathml(h: str) -> str:
    """Small MathML fixes so sans-serif math reads cleanly in browsers.

    * Multi-letter identifiers (max, sup, log) stay upright; only single letters are italic.
    * Norm and absolute-value bars get no operator spacing (browsers treat them as infix).
    * A minus right after =, a comma, an opening bracket or a relation is a sign, not a
      subtraction, so it gets no spacing either.
    """
    h = re.sub(r"<mi>([A-Za-z]{2,})</mi>", r'<mi mathvariant="normal">\1</mi>', h)
    h = re.sub(
        r"<mo(?![^>]*lspace)([^>]*)>(\u2225|\u2016|\||\u2223)</mo>",
        r'<mo\1 lspace="0em" rspace="0em">\2</mo>',
        h,
    )
    h = re.sub(
        r"(<mo[^>]*>(?:=|,|\(|\[|\u2248|\u2264|\u2265|&lt;|&gt;|<|>)</mo>)<mo>\u2212</mo>",
        r'\1<mo form="prefix" lspace="0em" rspace="0em">−</mo>',
        h,
    )
    return h


def strip_tags(s: str) -> str:
    return re.sub(r"<[^>]+>", "", s)


def build_index() -> None:
    cards = []
    for folder in sorted(p for p in EXPLAINERS.iterdir() if (p / "explainer.md").exists()):
        meta, _ = split_front_matter((folder / "explainer.md").read_text())
        poster = (
            next(iter(sorted((folder / "media").glob("*.png"))), None)
            if (folder / "media").exists()
            else None
        )
        img = (
            f'<img src="{folder.name}/media/{poster.name}" alt="" width="640" height="360" '
            f'loading="lazy">'
            if poster
            else ""
        )
        cards.append(
            f'<a class="ex-card" href="{folder.name}/index.html">{img}'
            f'<span class="label">{html.escape(meta.get("area", ""))}</span>'
            f"<h3>{html.escape(meta['title'])}</h3>"
            f"<p>{html.escape(meta['subtitle'])}</p></a>"
        )
    page = (TOOLS / "index_template.html").read_text().replace("{{cards}}", "\n".join(cards))
    (EXPLAINERS / "index.html").write_text(page)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("slugs", nargs="*")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--check", action="store_true", help="lint only, write nothing")
    a = ap.parse_args()
    folders = (
        sorted(p for p in EXPLAINERS.iterdir() if (p / "explainer.md").exists())
        if a.all
        else [EXPLAINERS / s for s in a.slugs]
    )
    if not folders:
        ap.error("give a slug or --all")
    failed = False
    for f in folders:
        rep = build_one(f, a.check)
        status = "FAIL" if rep.errors else "ok"
        print(f"[{status}] {f.name}")
        for e in rep.errors:
            print(f"  error: {e}")
        for w in rep.warnings:
            print(f"  warn:  {w}")
        failed |= bool(rep.errors)
    if not a.check and not failed:
        build_index()
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
