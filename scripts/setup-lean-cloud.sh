#!/usr/bin/env bash
# Cloud-session setup for ctrl's Lean code (paste into the environment's "Setup script").
# Works behind the Claude Code agent proxy: uses only github.com/<o>/<r>/releases/download/...
# (which redirects to release-assets.githubusercontent.com), anonymous git clones of public
# GitHub repos, and the Ubuntu apt mirror. Mathlib .olean source is chosen by MATHLIB_OLEANS:
#   cache    -> `lake exe cache get` (needs cache.mathlib.org allowed under Network access)
#   tarball  -> download a prebuilt .lake tarball from a GitHub release (set OLEAN_TARBALL_BASE)
#   source   -> build Mathlib from source in the background (several hours on 4 cores)
#   none     -> toolchain + sources only (enough for `lake env lean` on Mathlib-free files)
set -euo pipefail

REPO_DIR="${REPO_DIR:-ctrl}"            # setup script starts one directory above the repo
MATHLIB_OLEANS="${MATHLIB_OLEANS:-cache}"
OLEAN_TARBALL_BASE="${OLEAN_TARBALL_BASE:-}"   # e.g. https://github.com/OWNER/REPO/releases/download/mathlib-625d891
ELAN_VERSION="${ELAN_VERSION:-v4.1.2}"

cd "$REPO_DIR"
TC="$(tr -d '[:space:]' < lean-toolchain)"     # leanprover/lean4:v4.36.0-rc1
VER="${TC#*:}"                                 # v4.36.0-rc1
case "$(uname -m)" in
  x86_64)  ELAN_ARCH=x86_64-unknown-linux-gnu;  LEAN_SUFFIX=linux ;;
  aarch64) ELAN_ARCH=aarch64-unknown-linux-gnu; LEAN_SUFFIX=linux_aarch64 ;;
  *) echo "unsupported arch $(uname -m)" >&2; exit 1 ;;
esac

command -v zstd >/dev/null || { apt-get update -qq && apt-get install -y -qq zstd; }

# 1. elan (from its GitHub release; elan's own installer/updater needs release.lean-lang.org)
if [[ ! -x "$HOME/.elan/bin/elan" ]]; then
  t="$(mktemp -d)"
  curl -fsSL "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-${ELAN_ARCH}.tar.gz" | tar xz -C "$t"
  "$t/elan-init" -y --default-toolchain none --no-modify-path
  rm -rf "$t"
fi
export PATH="$HOME/.elan/bin:$PATH"
for b in elan lean lake leanc; do ln -sf "$HOME/.elan/bin/$b" "/usr/local/bin/$b" 2>/dev/null || true; done

# 2. Lean toolchain: unpack the GitHub release asset where elan expects it
#    (`elan toolchain install` fails: "failed to parse latest release tag").
TC_DIR="$HOME/.elan/toolchains/$(echo "$TC" | sed 's|/|--|; s|:|---|')"
if [[ ! -x "$TC_DIR/bin/lean" ]]; then
  t="$(mktemp -d)"
  curl -fsSL "https://github.com/leanprover/lean4/releases/download/${VER}/lean-${VER#v}-${LEAN_SUFFIX}.tar.zst" \
    | tar --zstd -x -C "$t"
  mkdir -p "$(dirname "$TC_DIR")"; rm -rf "$TC_DIR"; mv "$t"/lean-* "$TC_DIR"; rm -rf "$t"
fi
lean --version

# 3. Lake dependencies: shallow-fetch each package at its manifest rev (fast; avoids full
#    mathlib history clone). Lake accepts these as-is because the revs match the manifest.
python3 -I -c '
import json
for p in json.load(open("lake-manifest.json"))["packages"]:
    print(p["name"], p["url"], p["rev"])' | while read -r name url rev; do
  d=".lake/packages/$name"
  if [[ -d "$d/.git" ]] && [[ "$(git -C "$d" rev-parse HEAD 2>/dev/null)" == "$rev" ]]; then continue; fi
  rm -rf "$d"; mkdir -p "$d"
  git -C "$d" init -q; git -C "$d" remote add origin "$url"
  git -C "$d" fetch -q --depth 1 origin "$rev"; git -C "$d" checkout -q --detach FETCH_HEAD
done

# 4. Mathlib .oleans
case "$MATHLIB_OLEANS" in
  cache)
    lake exe cache get ;;
  tarball)
    [[ -n "$OLEAN_TARBALL_BASE" ]] || { echo "set OLEAN_TARBALL_BASE" >&2; exit 1; }
    # Parts produced by: tar -C .lake/packages --zstd -cf - */.lake/build | split -b 1900M - lake-build.tar.zst.part-
    # (built with the same Lean commit; Mathlib's cache hashes are platform-independent)
    for s in aa ab ac ad ae af ag ah; do
      curl -fsSL "$OLEAN_TARBALL_BASE/lake-build.tar.zst.part-$s" || break
    done | tar --zstd -x -C .lake/packages ;;
  source)
    # Too long for a setup script to block on; build in the background and log.
    nohup lake build > /tmp/lake-build.log 2>&1 & ;;
  none) ;;
esac
echo "Lean setup done ($MATHLIB_OLEANS)."
