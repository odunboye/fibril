#!/usr/bin/env bash
# Test this worktree's compiled package without overwriting Pack's shared cache.
set -euo pipefail
cd "$(dirname "$0")/.."

make -j8 build
paths=$(pack package-path)
compiler_package=$(printf '%s' "$paths" | tr ':' '\n' | grep '/idris2/idris2-' | head -1)
if [[ -z "$compiler_package" ]]; then
  echo 'Unable to locate Idris in the Pack package path.' >&2
  exit 1
fi
idris="$(dirname "$compiler_package")/bin/idris2"
ttc_version=${compiler_package##*/idris2-}
# The compiler package directory is versioned by Idris version, while build/ttc
# is versioned by TTC format. Require exactly one local TTC format directory.
ttc_dirs=(build/ttc/*)
if [[ ${#ttc_dirs[@]} -ne 1 || ! -d ${ttc_dirs[0]} ]]; then
  echo 'Expected exactly one local build/ttc format directory.' >&2
  exit 1
fi
format=$(basename "${ttc_dirs[0]}")
if [[ ! -x "$idris" ]]; then
  echo "Missing Idris executable for $ttc_version ($format)." >&2
  exit 1
fi

tmp=$(mktemp -d "${TMPDIR:-/tmp}/fibril-cubical-test.XXXXXXXX")
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/fibril-0.1.0/$format"
printf 'package fibril\nversion = 0.1.0\ndepends = yaml\n' > "$tmp/fibril-0.1.0/fibril.ipkg"
cp -R "${ttc_dirs[0]}/." "$tmp/fibril-0.1.0/$format/"
other_paths=$(printf '%s' "$paths" | tr ':' '\n' | grep -v '/fibril/' | paste -sd ':' -)
export IDRIS2_PACKAGE_PATH="$tmp:$other_paths"
cd test
"$idris" --build tests.ipkg
./build/exec/fibril-tests
cd negative
# Idris --check may return zero even when it reports a type error. Inspect the
# diagnostic as well as the status, and load the temporary package explicitly.
"$idris" -p fibril --check ForgeClosedPath.idr > "$tmp/forge.log" 2>&1 || true
if ! grep -q 'IndependentPath.MkCheckedClosedPath is private' "$tmp/forge.log"; then
  echo 'Negative opacity check failed for an unrelated reason:' >&2
  read -r -d '' output < "$tmp/forge.log" || true
  printf '%s\n' "$output" >&2
  exit 1
fi
echo 'Checked path opacity negative test passed.'
for fixture in PathCapturesCoreVariable PathEscapesDimension; do
  "$idris" -p fibril --check "$fixture.idr" > "$tmp/$fixture.log" 2>&1 || true
  if ! grep -Fq 'Mismatch between: S ?k and 0.' "$tmp/$fixture.log"; then
    echo "Negative scope test $fixture failed for an unrelated reason:" >&2
    read -r -d '' output < "$tmp/$fixture.log" || true
    printf '%s\n' "$output" >&2
    exit 1
  fi
done
echo 'Checked path scope negative tests passed.'
