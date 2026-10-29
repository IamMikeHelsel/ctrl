"""Small, reusable Manim scene conventions with real section boundaries."""

import json
import os
from pathlib import Path

from manim import Scene, Text, VGroup, RoundedRectangle, FadeIn, FadeOut, UP, DOWN

INK = "#25352F"
MUTED = "#66766E"
PAPER = "#FFFEF9"
GREEN = "#2F7A5C"
BLUE = "#3473A0"
ORANGE = "#B76B2F"


def words(value, size=28, color=INK):
    return Text(value, font="Arial", font_size=size, color=color)


def block(label, point, width=2.45, color=INK):
    shape = RoundedRectangle(
        width=width,
        height=1.05,
        corner_radius=0.12,
        color=color,
        stroke_width=2,
        fill_color=color,
        fill_opacity=0.05,
    )
    text = words(label, 26).move_to(shape)
    if text.width > width - 0.25:
        text.scale_to_fit_width(width - 0.25)
    return VGroup(shape, text).move_to(point)


class StoryScene(Scene):
    story_id = "example"
    story_title = "An explanation"
    summary = ""
    category = "Explanation"

    def setup(self):
        self.camera.background_color = PAPER
        self.notes = []
        self.footer = None
        heading = words(self.story_title, 33).to_edge(UP, buff=0.42)
        self.add(heading)

    def step(self, title, caption):
        """Start a separately playable section; preserve all earlier objects."""
        self.next_section(title)
        self.notes.append({"title": title, "caption": caption})
        footer = words(title, 25, MUTED).to_edge(DOWN, buff=0.38)
        if self.footer is not None:
            self.play(FadeOut(self.footer), FadeIn(footer), run_time=0.35)
        else:
            self.play(FadeIn(footer), run_time=0.35)
        self.footer = footer

    def hold(self, duration=1.25):
        self.wait(duration)

    def tear_down(self):
        target = os.environ.get("DIAGRAM_META_DIR")
        if target:
            Path(target).mkdir(parents=True, exist_ok=True)
            (Path(target) / f"{self.__class__.__name__}.json").write_text(
                json.dumps(
                    {
                        "id": self.story_id,
                        "title": self.story_title,
                        "summary": self.summary,
                        "category": self.category,
                        "kind": "video",
                        "steps": self.notes,
                        "source_derivation": getattr(self, "source_derivation", None),
                    },
                    indent=2,
                )
            )
