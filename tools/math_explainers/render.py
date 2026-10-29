"""Render sectioned Manim scenes; keep source hashes bound to each video."""

import argparse
import json
import os
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
CACHE = ROOT / "output/math-explainers/manim"
OUT = ROOT / "site/explainers/lab/exports"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--scene", action="append")
    args = parser.parse_args()
    env = {
        **os.environ,
        "DIAGRAM_META_DIR": str(CACHE / "metadata"),
        "PYTHONPATH": str(HERE / "scenes") + os.pathsep + os.environ.get("PYTHONPATH", ""),
    }
    for scene in args.scene or ["LyapunovWalkthrough", "BrakingWalkthrough", "KalmanWalkthrough"]:
        subprocess.run(
            [
                "manim",
                "render",
                "--media_dir",
                str(CACHE),
                "--save_sections",
                "--format",
                "mp4",
                "-qm",
                "--progress_bar",
                "none",
                "-v",
                "WARNING",
                str(HERE / "scenes/math_scenes.py"),
                scene,
            ],
            check=True,
            cwd=ROOT,
            env=env,
        )
        notes = json.loads((CACHE / "metadata" / f"{scene}.json").read_text())
        files = [
            p
            for p in CACHE.rglob(f"{scene}.json")
            if p.parent.name == "sections" and "720p30" in p.parts
        ]
        if len(files) != 1:
            raise RuntimeError(f"Ambiguous section manifest: {files}")
        manifest = files[0]
        sections = json.loads(manifest.read_text())
        if len(sections) != len(notes["steps"]):
            raise RuntimeError("Manim sections do not match captions")
        dest = OUT / notes["id"]
        dest.mkdir(parents=True, exist_ok=True)
        shutil.copy2(manifest.parent.parent / f"{scene}.mp4", dest / "complete.mp4")
        for i, (note, section) in enumerate(zip(notes["steps"], sections)):
            clip = dest / f"step-{i + 1:02}.mp4"
            poster = clip.with_suffix(".png")
            shutil.copy2(manifest.parent / section["video"], clip)
            subprocess.run(
                [
                    "ffmpeg",
                    "-v",
                    "error",
                    "-y",
                    "-sseof",
                    "-0.08",
                    "-i",
                    str(clip),
                    "-frames:v",
                    "1",
                    str(poster),
                ],
                check=True,
            )
            probe = json.loads(
                subprocess.check_output(
                    [
                        "ffprobe",
                        "-v",
                        "error",
                        "-show_entries",
                        "format=duration",
                        "-of",
                        "json",
                        str(clip),
                    ]
                )
            )
            note.update(
                video=f"exports/{notes['id']}/{clip.name}",
                poster=f"exports/{notes['id']}/{poster.name}",
                durationMs=round(float(probe["format"]["duration"]) * 1000),
            )
        (dest / "story.json").write_text(json.dumps(notes, indent=2) + "\n")
        print(f"Rendered {notes['id']}: {len(notes['steps'])} sections", flush=True)


if __name__ == "__main__":
    main()
