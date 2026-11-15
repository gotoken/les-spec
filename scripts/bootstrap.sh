#!/usr/bin/env bash
# Build the upstream Go CLI at exactly upstream/LES_COMMIT, isolated in .work/.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SHA="$(tr -d '\r\n' < "$ROOT/upstream/LES_COMMIT")"
if ! [[ "$SHA" =~ ^[0-9a-f]{40}$ ]]; then
  echo "Invalid upstream SHA: $SHA" >&2
  exit 2
fi
command -v git >/dev/null || { echo "git not installed" >&2; exit 2; }
command -v go >/dev/null || { echo "go not installed" >&2; exit 2; }
UP="$ROOT/.work/upstream-les"
mkdir -p "$ROOT/.work/bin"
if [[ ! -d "$UP/.git" ]]; then
  git clone https://github.com/unak/les.git "$UP"
fi
# Allow switching only the local isolated checkout, never the user's own source tree.
git -C "$UP" fetch origin "$SHA"
git -C "$UP" checkout --detach "$SHA"
ACTUAL="$(git -C "$UP" rev-parse HEAD)"
[[ "$ACTUAL" == "$SHA" ]] || { echo "SHA mismatch: $ACTUAL" >&2; exit 1; }
(cd "$UP" && go build -o "$ROOT/.work/bin/les" ./cmd/les)
echo "Built les CLI at $ACTUAL: $ROOT/.work/bin/les"
(cd "$ROOT/lesdump" && go build -o "$ROOT/.work/bin/lesdump" .)
echo "Built lesdump: $ROOT/.work/bin/lesdump"
