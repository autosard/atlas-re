#!/usr/bin/env bash
set -euo pipefail

# ---- config ----
BUNDLE_NAME="artifact/artifact/source"
VENDOR_DIR="artifact/vendor"   # where your tar.gz deps live

# ---- freeze for reproducibility ----
echo "==> Freezing dependency versions"
cabal build
cabal freeze

# ---- assemble bundle ----
echo "==> Assembling bundle"
mkdir -p "$BUNDLE_NAME"

# project files
cp -r ./*.cabal "$BUNDLE_NAME/" 2>/dev/null || true
cp -r cabal.project.freeze "$BUNDLE_NAME/" 2>/dev/null || true
cp -r artifact/cabal.project "$BUNDLE_NAME/" 2>/dev/null || true
cp -r src "$BUNDLE_NAME/" 2>/dev/null || true
cp -r app "$BUNDLE_NAME/" 2>/dev/null || true
cp -r test "$BUNDLE_NAME/" 2>/dev/null || true
cp -r examples "$BUNDLE_NAME/" 2>/dev/null || true
cp -r README "$BUNDLE_NAME/" 2>/dev/null || true

# vendor tarballs (like your haskell-z3 sdist)
if [ -d "$VENDOR_DIR" ]; then
  cp -r "$VENDOR_DIR" "$BUNDLE_NAME/"
fi

echo "==> Done"
