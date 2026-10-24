"""Render every manim scene of an explainer into site/explainers/<slug>/media/.

    uv run --no-project --python 3.12 --with manim==0.22.0 --with numpy \
        tools/explainer/render.py SLUG [--quality m|h|l] [--scene NAME]

For each `class Name(ExplainerScene)` in site/explainers/<slug>/scenes/*.py this writes
media/<Name>.mp4 (H.264, faststart, no audio) and media/<Name>.png (poster frame at the class's
`POSTER_AT` fraction of the runtime, default 0.5). Default quality is 720p30 to keep the repo small.

Needs a LaTeX install with `sansmath` and `dvisvgm` (MathTex), plus ffmpeg.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXPLAINERS = ROOT / "site" / "explainers"
SCENE_RE = re.compile(r"^class\s+(\w+)\((?:[\w.]*\.)?ExplainerScene\)", re.M)


def run(cmd: list[str], **kw) -> None:
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, check=True, **kw)


def duration(video: Path) -> float:
    res = subprocess.run(
        [
            "ffprobe",
            "-v",
            "error",
            "-show_entries",
            "format=duration",
            "-of",
            "csv=p=0",
            str(video),
        ],
        capture_output=True,
        text=True,
        check=True,
    )
    return float(res.stdout.strip())


def poster_fraction(source: str, name: str) -> float:
    """`POSTER_AT = 0.6` in the scene class picks the poster frame; default is mid-video."""
    body = source.split(f"class {name}(", 1)[1].split("\nclass ", 1)[0]
    m = re.search(r"POSTER_AT\s*=\s*([0-9.]+)", body)
    return float(m.group(1)) if m else 0.5


def frame(video: Path, t: float):
    import numpy as np  # manim's environment always has numpy

    res = subprocess.run(
        [
            "ffmpeg",
            "-loglevel",
            "error",
            "-ss",
            f"{t:.3f}",
            "-i",
            str(video),
            "-frames:v",
            "1",
            "-vf",
            "scale=320:180,format=gray",
            "-f",
            "rawvideo",
            "-",
        ],
        capture_output=True,
        check=True,
    )
    return np.frombuffer(res.stdout, dtype=np.uint8).astype(float)


def stillest_time(video: Path, target: float, span: float = 2.0, step: float = 0.25) -> float:
    """Poster frames caught mid-fade look broken. Pick the time near `target` where the
    picture changes least over the next 0.2 s."""
    total = duration(video)
    best, best_t = None, target
    t = max(0.0, target - span)
    while t <= min(total - 0.3, target + span):
        a, b = frame(video, t), frame(video, t + 0.2)
        diff = float(abs(a - b).mean()) + 0.01 * abs(t - target)
        if best is None or diff < best:
            best, best_t = diff, t
        t += step
    return best_t


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("slug")
    ap.add_argument("--quality", default="m", choices=["l", "m", "h"])
    ap.add_argument("--scene", action="append", help="render only these scene classes")
    a = ap.parse_args()

    folder = EXPLAINERS / a.slug
    out = folder / "media"
    out.mkdir(exist_ok=True)
    manim = shutil.which("manim") or sys.executable + " -m manim"
    for src in sorted((folder / "scenes").glob("*.py")):
        for name in SCENE_RE.findall(src.read_text()):
            if a.scene and name not in a.scene:
                continue
            with tempfile.TemporaryDirectory() as tmp:
                run(
                    [
                        *manim.split(),
                        f"-q{a.quality}",
                        "--disable_caching",
                        "--format=mp4",
                        "--media_dir",
                        tmp,
                        str(src),
                        name,
                    ],
                    cwd=ROOT,
                )
                video = next(Path(tmp).rglob(f"{name}.mp4"))
                dst = out / f"{name}.mp4"
                # Re-encode: small, web-safe, no audio track, moov atom up front.
                run(
                    [
                        "ffmpeg",
                        "-y",
                        "-loglevel",
                        "error",
                        "-i",
                        str(video),
                        "-an",
                        "-c:v",
                        "libx264",
                        "-preset",
                        "veryfast",
                        "-crf",
                        "26",
                        "-pix_fmt",
                        "yuv420p",
                        "-movflags",
                        "+faststart",
                        str(dst),
                    ]
                )
                at = poster_fraction(src.read_text(), name) * duration(dst)
                at = stillest_time(dst, at)
                run(
                    [
                        "ffmpeg",
                        "-y",
                        "-loglevel",
                        "error",
                        "-ss",
                        f"{at:.2f}",
                        "-i",
                        str(dst),
                        "-frames:v",
                        "1",
                        "-update",
                        "1",
                        str(out / f"{name}.png"),
                    ]
                )
                print(f"  -> {dst.relative_to(ROOT)} ({dst.stat().st_size // 1024} KB)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
