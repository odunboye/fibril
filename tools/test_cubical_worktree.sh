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
# Build tests in a fresh directory as well: test/build may contain TTCs linked
# against a different installed fibril package or be used by another run.
mkdir -p "$tmp/tests"
cp test/tests.ipkg "$tmp/tests/"
cp -R test/src test/negative "$tmp/tests/"
cd "$tmp/tests"
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
"$idris" -p fibril --check ForgeBoolPathType.idr > "$tmp/forge-type.log" 2>&1 || true
if ! grep -q 'IndependentPath.MkCheckedBoolPathType is private' "$tmp/forge-type.log"; then
  echo 'Negative path-type opacity check failed for an unrelated reason:' >&2
  read -r -d '' output < "$tmp/forge-type.log" || true
  printf '%s\n' "$output" >&2
  exit 1
fi
echo 'Checked path type opacity negative test passed.'
"$idris" -p fibril --check ForgeCheckedBool.idr > "$tmp/forge-bool.log" 2>&1 || true
if ! grep -q 'IndependentPath.MkCheckedClosedBool is private' "$tmp/forge-bool.log"; then
  echo 'Negative checked-Boolean opacity check failed for an unrelated reason:' >&2
  read -r -d '' output < "$tmp/forge-bool.log" || true
  printf '%s\n' "$output" >&2
  exit 1
fi
echo 'Checked endpoint opacity negative test passed.'
"$idris" -p fibril --check ForgeRuntimeCheckedBool.idr > "$tmp/forge-runtime.log" 2>&1 || true
if ! grep -q 'IndependentPath.MkRuntimeCheckedClosedBool is private' "$tmp/forge-runtime.log"; then
  echo 'Negative runtime endpoint opacity check failed for an unrelated reason:' >&2
  read -r -d '' output < "$tmp/forge-runtime.log" || true
  printf '%s\n' "$output" >&2
  exit 1
fi
echo 'Runtime checked endpoint opacity negative test passed.'
"$idris" -p fibril --check ForgeRuntimeInterface.idr > "$tmp/forge-interface.log" 2>&1 || true
if ! grep -q 'RuntimeInterface.Admitted is private' "$tmp/forge-interface.log"; then
  echo 'Negative runtime-interface opacity check failed for an unrelated reason:' >&2
  read -r -d '' output < "$tmp/forge-interface.log" || true
  printf '%s\n' "$output" >&2
  exit 1
fi
echo 'Runtime interface opacity negative test passed.'
for fixture in PathCapturesCoreVariable PathEscapesDimension OpenPathDimensionEscape OpenPathTermEscape ContextPathEscape ContextEndpointEscape ContextDimensionEscape ContextTermEscape ContextMappingEscape TelescopeCycle TelescopeDimensionEscape TelescopePathEscape TelescopeTermEscape SquareDimensionEscape; do
  "$idris" -p fibril --check "$fixture.idr" > "$tmp/$fixture.log" 2>&1 || true
  if ! grep -Fq 'Mismatch between: S ?k and 0.' "$tmp/$fixture.log"; then
    echo "Negative scope test $fixture failed for an unrelated reason:" >&2
    read -r -d '' output < "$tmp/$fixture.log" || true
    printf '%s\n' "$output" >&2
    exit 1
  fi
done
echo 'Checked path scope negative tests passed.'
"$idris" -p fibril --check ForgeContextAbstraction.idr > "$tmp/forge-context.log" 2>&1 || true
if ! grep -Fq 'PathContext.MkCheckedContextAbstraction is private' "$tmp/forge-context.log" || grep -Fq 'While processing type of bad' "$tmp/forge-context.log"; then
  echo 'Negative context witness opacity check failed for an unrelated reason:' >&2
  cat "$tmp/forge-context.log" >&2
  exit 1
fi
"$idris" -p fibril --check ContextAbstractionMismatch.idr > "$tmp/context-mismatch.log" 2>&1 || true
if ! grep -Fq 'While processing right hand side of bad. When unifying:' "$tmp/context-mismatch.log" || ! grep -Fq 'Mismatch between:' "$tmp/context-mismatch.log" || grep -Fq 'While processing type of bad' "$tmp/context-mismatch.log"; then
  echo 'Negative context mismatch check failed for an unrelated reason:' >&2
  cat "$tmp/context-mismatch.log" >&2
  exit 1
fi
echo 'Context witness opacity and context mismatch negative tests passed.'

"$idris" -p fibril --check ForgeSquare.idr > "$tmp/forge-square.log" 2>&1 || true
if ! grep -Fq 'Square.MkCheckedSquare is private' "$tmp/forge-square.log" || grep -Fq 'While processing type of bad' "$tmp/forge-square.log"; then
  echo 'Square witness opacity test failed:' >&2
  cat "$tmp/forge-square.log" >&2
  exit 1
fi
"$idris" -p fibril --check SquareMismatch.idr > "$tmp/square-mismatch.log" 2>&1 || true
if ! grep -Fq 'While processing right hand side of bad. When unifying:' "$tmp/square-mismatch.log" || ! grep -Fq 'Mismatch between:' "$tmp/square-mismatch.log" || grep -Fq 'While processing type of bad' "$tmp/square-mismatch.log"; then
  echo 'Square witness mismatch test failed:' >&2
  cat "$tmp/square-mismatch.log" >&2
  exit 1
fi
echo 'Square witness opacity and mismatch negative tests passed.'
"$idris" -p fibril --check ForgeReusablePath.idr > "$tmp/forge-reusable.log" 2>&1 || true
if ! grep -Fq 'ReusablePath.MkCheckedPath is private' "$tmp/forge-reusable.log" || grep -Fq 'While processing type of bad' "$tmp/forge-reusable.log"; then
  cat "$tmp/forge-reusable.log" >&2; exit 1
fi
"$idris" -p fibril --check ReusablePathMismatch.idr > "$tmp/reusable-mismatch.log" 2>&1 || true
if ! grep -Fq 'While processing right hand side of bad. When unifying:' "$tmp/reusable-mismatch.log" || ! grep -Fq 'Mismatch between:' "$tmp/reusable-mismatch.log" || grep -Fq 'While processing type of bad' "$tmp/reusable-mismatch.log"; then
  cat "$tmp/reusable-mismatch.log" >&2; exit 1
fi
echo 'Reusable path opacity and mismatch negative tests passed.'
"$idris" -p fibril --check ReusablePathContextMismatch.idr > "$tmp/reusable-context.log" 2>&1 || true
if ! grep -Fq 'While processing right hand side of bad. When unifying:' "$tmp/reusable-context.log" || ! grep -Fq 'Mismatch between:' "$tmp/reusable-context.log" || grep -Fq 'While processing type of bad' "$tmp/reusable-context.log"; then
  cat "$tmp/reusable-context.log" >&2; exit 1
fi
echo 'Reusable path context mismatch negative test passed.'
"$idris" -p fibril --check SquareApplicationMismatch.idr > "$tmp/square-application-mismatch.log" 2>&1 || true
if ! grep -Fq 'While processing right hand side of bad. When unifying:' "$tmp/square-application-mismatch.log" || ! grep -Fq 'Mismatch between:' "$tmp/square-application-mismatch.log" || grep -Fq 'While processing type of bad' "$tmp/square-application-mismatch.log"; then
  cat "$tmp/square-application-mismatch.log" >&2; exit 1
fi
echo 'Square application endpoint mismatch negative test passed.'
for negative in ScopedSyntaxDimensionEscape ScopedSyntaxTermEscape; do
  "$idris" -p fibril --check "$negative.idr" > "$tmp/$negative.log" 2>&1 || true
  if ! grep -q 'Mismatch between: S .* and 0' "$tmp/$negative.log"; then
    echo "Scoped syntax negative test failed for an unrelated reason: $negative" >&2
    cat "$tmp/$negative.log" >&2
    exit 1
  fi
done
echo 'Uniform syntax scope escape negative tests passed.'
for fixture in TypedPathBadEndpoint TypedPathNonDimension TypedPathAnnotation TypedPathScope; do
  case $fixture in
    TypedPathBadEndpoint) expected='Mismatch between: FS FZ and FZ.' ;;
    TypedPathNonDimension) expected='Mismatch between: Bool and Interval' ;;
    TypedPathAnnotation) expected='Mismatch between: Universe and Path' ;;
    TypedPathScope) expected='Mismatch between: S ?k and 0.' ;;
  esac
  "$idris" -p fibril --check "$fixture.idr" > "$tmp/$fixture.log" 2>&1 || true
  if ! grep -Fq 'Error: While processing' "$tmp/$fixture.log" || ! grep -Fq "$expected" "$tmp/$fixture.log"; then
    echo "Negative typed-path test $fixture failed for an unrelated reason:" >&2
    cat "$tmp/$fixture.log" >&2
    exit 1
  fi
done
echo 'Typed path boundary, annotation, dimension and scope negative tests passed.'

for fixture in TypedNeutralWrongEndpoint TypedNeutralFalseFace; do
  case $fixture in
    TypedNeutralWrongEndpoint)
      expected='Mismatch between: FZ and FS FZ.'
      context='NeutralEqual [PathBetween FZ (FS FZ)] (SEndpoint FZ False) (NApply (NPath FZ) (Var FZ)) (NBase (FS FZ)) NType'
      ;;
    TypedNeutralFalseFace)
      expected='Mismatch between: True and False.'
      context='NeutralEqual [PathBetween FZ (FS FZ)] STop (NApply (NPath FZ) (Var FZ)) (NBase FZ) NType'
      ;;
  esac
  "$idris" -p fibril --check "$fixture.idr" > "$tmp/$fixture.log" 2>&1 || true
  if ! grep -Fq 'Error: While processing right hand side of bad.' "$tmp/$fixture.log" ||
     grep -Fq 'While processing type of bad' "$tmp/$fixture.log" ||
     ! grep -Fq "$expected" "$tmp/$fixture.log" ||
     ! grep -Fq "$context" "$tmp/$fixture.log"; then
    echo "Negative neutral path test $fixture failed for an unrelated reason:" >&2
    cat "$tmp/$fixture.log" >&2
    exit 1
  fi
done
echo 'Neutral path wrong-endpoint and false-face negative tests passed.'
