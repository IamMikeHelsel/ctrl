#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
docker run --rm --network none -v "$PWD:/manim" \
  manimcommunity/manim@sha256:3c3ce944c09d6fa73de59fe1e7a95e334e193ae9c2275d65937054e675f87b03 \
  manim --resolution 1280,720 --fps 24 --disable_caching \
  --media_dir animation/media animation/tracking.py ChangingPlans -o changing-plans.mp4
cp animation/media/videos/tracking/720p24/changing-plans.mp4 animation/changing-plans.mp4
