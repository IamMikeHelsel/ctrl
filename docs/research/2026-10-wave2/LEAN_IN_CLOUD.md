# LEAN-CLOUD: can cloud sessions build and check ctrl's Lean code?

Lane LEAN-CLOUD, 2026-10-24. Container: x86_64, 4 CPUs, 15 GB RAM, about 18 to 25 GB free disk.
The CPU was heavily shared with other wave-2 lanes the whole time (load average 23 to 31 on 4 cores), so the build timings below are pessimistic.

## Bottom line

- **The Lean toolchain works today with no settings change.** `github.com/<owner>/<repo>/releases/download/...` is allowed (it redirects to `release-assets.githubusercontent.com`, which is also allowed). I installed elan v4.1.2 and Lean v4.36.0-rc1 (the exact pin), shallow-fetched all 9 Lake dependencies at their manifest revs, and elaborated a file against Mathlib .oleans I built here. A cold start takes **about 46 s** (measured) and **3.1 GB** of disk.
- **Mathlib .oleans are the blocker.** `lake exe cache get` at the pinned Mathlib (625d891, 2026-10-16) reads from `https://cache.mathlib.org`, and the proxy denies it with `CONNECT 403`. I confirmed this: the run made 0 of 9047 downloads. The legacy fallback, `lakecache.blob.core.windows.net`, is also denied.
- **ctrl needs all of Mathlib.** `ControlsLean/Bounty/ErdosWave2.lean`, `Estimation/POMDPBelief.lean`, `Bounty/ErdosNewInsights.lean` and `Bounty/ErdosBounties.lean` say `import Mathlib`, and `Controls/BacksteppingCLF.lean` says `import Mathlib.Tactic`. So `lake build` / `scripts/check.sh` needs the full Mathlib build: about 8,637 Mathlib modules, 9,047 cache units in total.
- **A from-source build was not feasible within the hour.** I did **not** build ControlsLean or run `scripts/check.sh`.
- **The fix is one allowlist entry: `cache.mathlib.org`.** No-allowlist fallback: publish a prebuilt `.lake` build tarball as a GitHub release asset, which downloads through the allowed path.

## 1. What the user can configure (from the environment docs)

- **Network access.** Open the cloud environment menu in the session title bar, choose **Edit**, then **Network access**. Either pick a broader access level, or add hosts under **Allowed domains** (shown under the *Limited* level; older apps show it under *Custom*). Leave **Allow package managers** ticked. The docs link to https://code.claude.com/docs/en/cloud-environments#network-access.
- **Setup script.** In the same Edit dialog, under **Setup script**, the script runs when each new session starts.
  - It starts **one directory above the repository**, so it must `cd ctrl` first.
  - It **cannot read the environment's saved variables or secrets**.
  - Fixed scripts apply to new sessions.
- **Dependencies.** Install them in-session when you can, and make them persistent by putting the install commands in the setup script.
- **Custom container images.** The pages I read do not document any custom container image option. They only cover network access and the setup script.
- **Self-hosted pools and Remote Control.** The session tools mention self-hosted environment pools (`ccpool_` environment ids). Remote Control (`claude remote-control` in a terminal, or the Claude Desktop app) runs sessions on the user's own machine.

## 2. Toolchain: what works and what does not (all tested)

| Source | Result |
|---|---|
| `curl https://github.com/leanprover/elan/releases/download/v4.1.2/elan-x86_64-unknown-linux-gnu.tar.gz` | **works** (302 to release-assets.githubusercontent.com, 5 MB) |
| `curl https://github.com/leanprover/lean4/releases/download/v4.36.0-rc1/lean-4.36.0-rc1-linux.tar.zst` | **works**: 606 MB in 8 s, 3.1 GB unpacked. The `linux_aarch64` asset also resolves (302). |
| `raw.githubusercontent.com/leanprover/elan/master/elan-init.sh` | works (200) |
| `git clone` / shallow `git fetch <sha>` of public GitHub repos | **works**: all 9 manifest packages in 17 s, mathlib checkout 153 MB |
| `gh api` / `gh release download` | **fails**. GH_TOKEN is invalid for unattached repos. `add_repo` (read) says public repos get anonymous git reads only, with no API access. Direct curl of the download URL makes gh unnecessary. |
| `api.github.com`, `github.com/.../releases/latest`, `.../releases/tag/...` (HTML) | 403 from the proxy (path-filtered) |
| `release.lean-lang.org`, `releases.lean-lang.org`, `reservoir.lean-lang.org`, `mathlib4.lean-lang.org` | CONNECT 403 (blocked) |
| `elan toolchain install leanprover/lean4:v4.36.0-rc1` | **fails**: `error: failed to parse latest release tag`. elan's binary refers to `https://release.lean-lang.org` and to GitHub release-page lookups, and both are blocked. |
| Unpacking the release tarball to `~/.elan/toolchains/leanprover--lean4---v4.36.0-rc1` | **works**. elan lists it, and `lean --version` in the repo reports `4.36.0-rc1 ... commit c9afcddf`. |
| `apt-get install zstd` | works (the Ubuntu mirror is reachable) |

The quick-start in `AGENTS.md` (`elan-init.sh ... --default-toolchain none`, then `lake exe cache get`) fails here at two points:
- elan cannot auto-install the pinned toolchain.
- `cache get` is blocked.

Building Lean from source is unnecessary, because the release asset works.

## 3. Mathlib .oleans

- **Cache host.** The pinned Mathlib's `Cache/Infra.lean` sets `publicCacheEndpoint := "https://cache.mathlib.org"`. The legacy endpoint is `azureAccountURL := "https://lakecache.blob.core.windows.net"`, used with `MATHLIB_CACHE_DEBUG_USE_LEGACY`. The static curl it downloads comes from `github.com/leanprover-community/static-curl/releases/download/...`, which is allowed.
- **Configurable.** `MATHLIB_CACHE_BASE_URL` is a full mirror of the `{base}/{container}/{key}` layout. `MATHLIB_CACHE_GET_URL` is a single flat URL serving `{hash}.ltar`, and `MATHLIB_CACHE_DIR` is also settable.
  - A GitHub release cannot serve as a `GET_URL` mirror. It would need about 9,047 assets, and GitHub allows roughly 1,000 assets per release.
  - I found **no public GitHub-hosted mirror** of the Mathlib cache.
- **Lake's own Reservoir fetch.** Lake tries `reservoir.lean-lang.org` during `lake build`. The request is denied, but this is harmless: the build carries on.
- **Platform independence.** Mathlib's cache hash covers file contents, imports and `Lean.githash`, with no platform component (`Cache/Hashing.lean`). So .oleans built on another OS or architecture with the same Lean commit should be reusable. That is the premise of the tarball route.
  - Not verified end-to-end here. I did not have an ARM64-built tarball to test.

### From-source timing sample (measured)

- `timeout 1200 lake build Mathlib` ran for 20 min wall.
  - It built **510 modules** (Batteries, Aesop, Qq, ImportGraph, Mathlib.Tactic infrastructure).
  - It used **1,032 CPU-seconds**, about 2 CPU-s per module.
  - Because of contention from other lanes it got only about 0.86 of the 4 cores.
- These early infrastructure modules are lighter than typical Mathlib modules. Per-module wall times late in the sample were 10 to 60 s under contention.
- **Estimate** (an extrapolation, not a measurement):
  - Full Mathlib is about 15 to 30 CPU-hours.
  - That is **4 to 8 h wall on 4 dedicated cores**, and much longer on a shared container like this one.
  - Disk is about 5 to 6 GB of build output. The repo's `docker/erdos-lab.Dockerfile` also says "~5 GB".
- **Pipeline check.** `lake env lean` on a small file importing `Mathlib.Tactic.Choose` (built in the sample) elaborated in 5.7 s, and `#print axioms` worked. Toolchain, Lake and Mathlib .oleans work together end to end.
- **Not done:** building ControlsLean, and running `scripts/check.sh` in the copy. Both need the full Mathlib build. Never attempted on `/home/user/ctrl`.

## 4. Deliverables

### (b) Minimal allowlist (recommended path)

| Host | Why |
|---|---|
| `cache.mathlib.org` | **Required.** `lake exe cache get` downloads the about 9,047 prebuilt `.ltar` files for the pinned Mathlib and its dependencies from here. Without it the only option is the multi-hour source build. |
| `lakecache.blob.core.windows.net` | Optional. Legacy cache endpoint (`MATHLIB_CACHE_DEBUG_USE_LEGACY=1`), useful only as a fallback. |
| `release.lean-lang.org` | Optional. Lets plain `elan toolchain install` and elan auto-install work, so the manual tarball step is not needed. Not verified: elan also needs GitHub release HTML pages, which the proxy filters. The script below does not need it. |
| `reservoir.lean-lang.org` | Optional. Removes Lake's harmless Reservoir-fetch denial noise. Not needed. |

Not needed: `github.com` release downloads, `release-assets.githubusercontent.com` and git clones already work.

### (a)/(b) Setup script (paste into Setup script)

- **Default `MATHLIB_OLEANS=cache`.** Works once `cache.mathlib.org` is allowed.
- **Today, without any allowlist change:**
  - `MATHLIB_OLEANS=none` gives a working toolchain and sources.
  - `MATHLIB_OLEANS=tarball` with `OLEAN_TARBALL_BASE` works once a tarball is published.
  - Because the setup script cannot read the environment's saved variables, set these by editing the defaults at the top of the script.
- **Tested in a fresh `$HOME`.** Steps 1 to 3 (elan, toolchain, deps) completed in 45.8 s with `MATHLIB_OLEANS=none`. The `cache` branch is the standard Mathlib command and fails here only on the network denial. The `tarball` branch is untested because no tarball exists yet.

```bash
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
```

After setup, `scripts/check.sh` should run unchanged:
- `scripts/ensure_cache.sh` passes because `.lake/packages/mathlib` exists.
- `lean` and `lake` are on PATH through the `/usr/local/bin` symlinks.

The script is also saved at `scripts/setup-lean-cloud.sh`.

**No-allowlist route (tarball).** On the machine that already has a populated `.lake`, run the following and upload the parts as assets of a release on any public GitHub repo:

```bash
tar -C .lake/packages --zstd -cf - */.lake/build | split -b 1900M - lake-build.tar.zst.part-
```

The release asset path (`github.com/OWNER/REPO/releases/download/TAG/...`) is reachable from here.
- Per-asset limit: 2 GB.
- The tarball must be rebuilt whenever the Mathlib pin or toolchain changes.
- If the repo is private, anonymous download will fail.
- This route is a new publishing step, so it is the user's call.

### (c) Cold-start time and disk per path

| Path | Cold start | Disk | Status |
|---|---|---|---|
| Toolchain + deps only (`none`) | about 46 s (measured) | 3.1 GB toolchain + 174 MB sources | **works today** |
| `cache` (allow `cache.mathlib.org`) | about 46 s + roughly 2 to 5 min for cache get (AGENTS.md says "~2 min"). Downloads are an estimated 1 to 2 GB of .ltar. | about 9 GB total (3.1 + about 5 to 6 GB oleans) | blocked today on one host |
| `tarball` (GitHub release asset) | about 46 s + download at the observed rate (606 MB in 8 s, so a few GB in under 1 min) + zstd unpack, about 1 to 3 min | about 9 GB, plus about 2 GB transient if not streamed (the script streams) | works today once someone publishes the tarball; untested |
| `source` (build Mathlib in-container) | estimated 4 to 8 h on 4 dedicated cores; much longer when the container CPU is shared (measured 510 modules / 20 min at about 0.86 effective cores) | about 9 GB | feasible but impractical per session |

After the oleans exist, building ctrl's own 55 `ControlsLean` files should take minutes. I did not measure this.

### (d) Long-term recommendation

1. **Short term (minutes of user effort):** add `cache.mathlib.org` to Allowed domains and paste the setup script. This matches upstream Mathlib exactly and needs no maintenance as the pin moves, as long as the pin is a published Mathlib commit or tag.
2. **If the user will not widen the allowlist:** use the GitHub-release tarball. It is cheap, but must be republished on every Mathlib bump. Making that automatic would mean adding a release-publishing job, which is the user's decision.
3. **Self-hosted runner / Remote Control vs prebuilt image:**
   - For *checking in CI*, the existing self-hosted ARM64 runner is already the right answer. It keeps a warm `.lake`, and nothing here changes that.
   - For *interactive proving sessions*, the best experience is a session on the user's own machine through Remote Control, or a self-hosted environment pool if one is available. The `.lake` is warm, there is no allowlist, and there is no per-session download.
   - A prebuilt container image would be equivalent, but the environment docs I read describe no custom-image option. Do not plan on it until confirmed.
   - Among cloud sessions, the allowlist + setup script path has the lowest maintenance.

## Honesty notes

- **Measured:**
  - Toolchain and dependency download and install times.
  - The cache-host denial (0/9047).
  - The 20-minute build sample.
  - The smoke elaboration.
- **Estimated:**
  - The full Mathlib build time (extrapolated from light early modules plus general knowledge).
  - The cache-get duration and download size.
  - Olean disk size (from the repo's Dockerfile comment).
- **Not verified:**
  - That ARM64-built oleans load on x86_64. Inferred from Mathlib's platform-free cache hash.
  - That allowing `release.lean-lang.org` alone fixes `elan toolchain install`.
  - Any custom-image support.
- **Left in the scratchpad** for later lanes:
  - Toolchain at `/root/.elan` (3.1 GB, with `/usr/local/bin` symlinks).
  - The repo copy with a partial Mathlib build (about 700 MB) at `(session scratch copy, not committed)`.
  - `/home/user/ctrl` was not modified.
