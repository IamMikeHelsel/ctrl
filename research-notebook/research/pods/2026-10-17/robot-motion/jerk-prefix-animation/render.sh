#!/bin/sh
set -eu
cd "$(dirname "$0")"
image='manimcommunity/manim@sha256:3c3ce944c09d6fa73de59fe1e7a95e334e193ae9c2275d65937054e675f87b03'
# Fail if the existing pinned image is absent; never pull an image here.
docker image inspect "$image" >/dev/null
python3 exact_check.py
docker run --rm --pull never --network none -v "$PWD:/manim" "$image" \
  manim --resolution 1280,720 --fps 24 --disable_caching \
  --media_dir media prefix.py JerkPrefix -o jerk-prefix.mp4
cp media/videos/prefix/720p24/jerk-prefix.mp4 jerk-prefix.mp4
ffmpeg -y -sseof -0.1 -i jerk-prefix.mp4 -frames:v 1 -update 1 jerk-prefix-still.png
python3 record_outputs.py
