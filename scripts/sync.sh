#!/usr/bin/env bash
# Mirror sources (not build artifacts) to the Google Drive "lean" folder.
set -euo pipefail
cd "$(dirname "$0")/.."
DEST="$HOME/Library/CloudStorage/GoogleDrive-mhelsel@gmail.com/My Drive/lean/ControlsLean"
mkdir -p "$DEST"
rsync -a --delete \
  --exclude '.lake/' --exclude '.git/' --exclude '.github/' \
  ./ "$DEST/"
echo "Synced to $DEST"
