"""Shared helpers for the ctrl site animations: fonts, palette, overlays, GIF encoding."""
from __future__ import annotations

import os
import subprocess
from pathlib import Path

os.environ.setdefault("MUJOCO_GL", "egl")
os.environ.setdefault("EGL_PLATFORM", "surfaceless")
os.environ.setdefault("LIBGL_ALWAYS_SOFTWARE", "1")

from PIL import Image, ImageDraw, ImageFont  # noqa: E402

W, H = 800, 450
FPS = 12

INTER = "/usr/share/fonts/opentype/inter/Inter-{}.otf"
MONO = "/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf"


def font(size: int, weight: str = "Regular") -> ImageFont.FreeTypeFont:
    return ImageFont.truetype(INTER.format(weight), size)


def mono(size: int) -> ImageFont.FreeTypeFont:
    return ImageFont.truetype(MONO, size)


# Palette (matches the site's dark theme)
BG = (11, 15, 23)
PANEL = (17, 24, 39)
TEXT = (243, 244, 246)
MUTED = (156, 163, 175)
TEAL = (45, 212, 191)
AMBER = (251, 191, 36)
ROSE = (251, 113, 133)
BLUE = (96, 165, 250)


def ease(x: float) -> float:
    x = min(max(x, 0.0), 1.0)
    return x * x * (3 - 2 * x)


def alpha(c, a):
    return (*c, int(255 * max(0.0, min(1.0, a))))


def panel(draw: ImageDraw.ImageDraw, box, a=0.78, radius=10, outline=None):
    draw.rounded_rectangle(box, radius=radius, fill=alpha(PANEL, a),
                           outline=outline if outline else alpha((38, 50, 68), a), width=1)


def text(draw, xy, s, f, fill=TEXT, a=1.0, anchor="la"):
    draw.text(xy, s, font=f, fill=alpha(fill, a), anchor=anchor)


def compose(base: Image.Image) -> tuple[Image.Image, ImageDraw.ImageDraw]:
    layer = Image.new("RGBA", base.size, (0, 0, 0, 0))
    return layer, ImageDraw.Draw(layer)


def flatten(base: Image.Image, layer: Image.Image) -> Image.Image:
    return Image.alpha_composite(base.convert("RGBA"), layer).convert("RGB")


def bar(draw, x, y, w, h, frac, color, a=1.0, bg=(38, 50, 68)):
    draw.rounded_rectangle((x, y, x + w, y + h), radius=h // 2, fill=alpha(bg, a))
    fw = max(0, min(w, int(w * frac)))
    if fw >= h:
        draw.rounded_rectangle((x, y, x + fw, y + h), radius=h // 2, fill=alpha(color, a))


def encode_gif(frame_dir: Path, out: Path, fps: int = FPS, colors: int = 160) -> int:
    pal = frame_dir / "palette.png"
    pattern = str(frame_dir / "f%04d.png")
    subprocess.run(["ffmpeg", "-v", "error", "-y", "-framerate", str(fps), "-i", pattern,
                    "-vf", f"palettegen=max_colors={colors}:stats_mode=full", str(pal)], check=True)
    subprocess.run(["ffmpeg", "-v", "error", "-y", "-framerate", str(fps), "-i", pattern, "-i", str(pal),
                    "-lavfi", "paletteuse=dither=bayer:bayer_scale=4:diff_mode=rectangle",
                    "-loop", "0", str(out)], check=True)
    return out.stat().st_size


def project(scene, p, w=W, h=H):
    """Project a world point to pixel coords using the renderer's GL camera (perspective)."""
    import numpy as np
    cam = scene.camera[0]
    pos, fwd, up = np.array(cam.pos), np.array(cam.forward), np.array(cam.up)
    right = np.cross(fwd, up)
    d = np.asarray(p, float) - pos
    z = d @ fwd
    if z <= 1e-6:
        return None
    x, y = (d @ right) * cam.frustum_near / z, (d @ up) * cam.frustum_near / z
    top, bot = cam.frustum_top, cam.frustum_bottom
    half_w = (top - bot) / 2 * (w / h)
    sx = w / 2 + (x - cam.frustum_center) / half_w * (w / 2)
    sy = h * (1 - (y - bot) / (top - bot))
    return sx, sy


def add_arrow(scene, frm, to, rgba, width=0.018, kind="arrow"):
    import mujoco
    import numpy as np
    if scene.ngeom >= scene.maxgeom:
        return
    g = scene.geoms[scene.ngeom]
    t = mujoco.mjtGeom.mjGEOM_ARROW if kind == "arrow" else mujoco.mjtGeom.mjGEOM_CAPSULE
    mujoco.mjv_initGeom(g, t, np.zeros(3), np.zeros(3), np.zeros(9), np.array(rgba, dtype=np.float32))
    mujoco.mjv_connector(g, t, width, np.array(frm, float), np.array(to, float))
    g.emission = 0.5
    scene.ngeom += 1
