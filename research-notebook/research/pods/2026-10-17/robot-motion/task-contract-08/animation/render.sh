#!/bin/sh
set -eu
cd "$(dirname "$0")"
image='manimcommunity/manim@sha256:3c3ce944c09d6fa73de59fe1e7a95e334e193ae9c2275d65937054e675f87b03'
docker image inspect "$image" >/dev/null
python3 check_display.py
docker run --rm --pull never --network none -v "$PWD:/manim" "$image" \
  manim --resolution 1280,720 --fps 24 --disable_caching \
  --media_dir media position_task.py PositionTask -o position-task.mp4
cp media/videos/position_task/720p24/position-task.mp4 position-task.mp4
ffmpeg -y -sseof -0.1 -i position-task.mp4 -frames:v 1 -update 1 position-task-still.png
