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
for fixture in ShadowCommonWrongType ShadowCommonWrongContext; do
  case "$fixture" in
    ShadowCommonWrongType) expected='CommonHasType [] (CBool True) LUnit' ;;
    ShadowCommonWrongContext) expected='CommonHasType [LUnit] (CVar FZ) LBool' ;;
  esac
  "$idris" -p fibril --check "$fixture.idr" > "$tmp/$fixture.log" 2>&1 || true
  if [[ $(grep -c '^Error:' "$tmp/$fixture.log") -ne 1 ]] ||
     ! grep -Fq 'Error: While processing right hand side of bad. When unifying:' "$tmp/$fixture.log" ||
     ! grep -Fq "$expected" "$tmp/$fixture.log" ||
     ! grep -Fq 'Mismatch between: LBool and LUnit.' "$tmp/$fixture.log" ||
     grep -Eq 'Undefined name|While processing type of' "$tmp/$fixture.log"; then
    echo "Common judgment negative test failed for an unrelated reason: $fixture" >&2
    cat "$tmp/$fixture.log" >&2
    exit 1
  fi
done
echo 'Common judgment wrong type and context negative tests passed.'
for fixture in CommonFaceWrongFace CommonFaceWrongIndex CommonFaceWrongType CommonFaceUsesReflection; do
  "$idris" -p fibril --check "$fixture.idr" > "$tmp/$fixture.log" 2>&1 || true
  case "$fixture" in
    CommonFaceWrongFace) expected='boundedFaceEntails (the (ScopedFace 1) (SEndpoint FZ True)) (scopedEndpoint (Var FZ) False)' ;;
    CommonFaceWrongIndex) expected='Mismatch between: FZ and FS FZ.' ;;
    CommonFaceWrongType) expected='Mismatch between: LBool and LUnit.' ;;
    CommonFaceUsesReflection) expected='Uses (the (Term [BoolTy] BoolTy) (Ref Here)) [Erased]' ;;
  esac
  if [[ $(grep -c '^Error:' "$tmp/$fixture.log") -ne 1 ]] ||
     ! grep -Fq 'Error: While processing right hand side of bad.' "$tmp/$fixture.log" ||
     ! grep -Fq "$expected" "$tmp/$fixture.log" ||
     grep -Eq 'Undefined name|While processing type of' "$tmp/$fixture.log"; then
    echo "Common face equality negative test failed for an unrelated reason: $fixture" >&2
    cat "$tmp/$fixture.log" >&2; exit 1
  fi
  if [[ $fixture == CommonFaceUsesReflection ]] && ! grep -Fq 'Mismatch between: CommonFaceEqual' "$tmp/$fixture.log"; then
    echo 'Common face equality reflection fixture did not reject the intended judgment.' >&2
    cat "$tmp/$fixture.log" >&2; exit 1
  fi
done
echo 'Common face equality wrong face, index, type, and Uses reflection tests passed.'
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

for fixture in TypedPathPBadFamily TypedPathPNonBoolean TypedPathPScope; do
  "$idris" -p fibril --check "$fixture.idr" > "$tmp/$fixture.log" 2>&1 || true
  case $fixture in
    TypedPathPBadFamily) expected='Mismatch between: NType and NBase' ; location='right hand side' ;;
    TypedPathPNonBoolean) expected='Mismatch between: True and False' ; location='right hand side' ;;
    TypedPathPScope) expected='Mismatch between: S ?k and 0' ; location='type' ;;
  esac
  if ! grep -Fq "While processing $location of bad" "$tmp/$fixture.log" || ! grep -Fq "$expected" "$tmp/$fixture.log"; then
    echo "PathP negative test $fixture failed for an unrelated reason:" >&2
    cat "$tmp/$fixture.log" >&2; exit 1
  fi
done
echo 'PathP family, non-Boolean face, and dimension scope negative tests passed.'

for fixture in TypedPathPOpenEndpoint TypedPathPBadBody TypedPathPBadBoundary; do
  "$idris" -p fibril --check "$fixture.idr" > "$tmp/$fixture.log" 2>&1 || true
  case $fixture in
    TypedPathPOpenEndpoint) expected='Mismatch between: Zero and Var FZ.' ;;
    TypedPathPBadBody) expected='Mismatch between: NType and NPathType' ;;
    TypedPathPBadBoundary) expected='Mismatch between: Var (FS FZ) and Zero.' ;;
  esac
  if ! grep -Fq 'While processing right hand side of bad' "$tmp/$fixture.log" ||
     [[ $(grep -c '^Error:' "$tmp/$fixture.log") -ne 1 ]] ||
     grep -Fq 'While processing type of bad' "$tmp/$fixture.log" ||
     ! grep -Fq "$expected" "$tmp/$fixture.log"; then
    echo "PathP dependent premise test $fixture failed for an unrelated reason:" >&2
    cat "$tmp/$fixture.log" >&2; exit 1
  fi
done
echo 'PathP instantiated endpoint, body, and boundary negative tests passed.'

for fixture in TypedTypeCongUnrelated TypedTypeCongFace TypedTypeCongMalformed TypedTypeCongScope; do
  "$idris" -p fibril --check "$fixture.idr" > "$tmp/$fixture.log" 2>&1 || true
  location='right hand side'
  case $fixture in
    TypedTypeCongUnrelated) expected='Mismatch between: FZ and FS FZ.' ;;
    TypedTypeCongFace) expected='Mismatch between: SBottom and STop.' ;;
    TypedTypeCongMalformed) expected='Mismatch between: NType and NBase FZ.' ;;
    TypedTypeCongScope) expected='Mismatch between: S ?k and 0.'; location='type' ;;
  esac
  if ! grep -Fq "While processing $location of bad" "$tmp/$fixture.log" ||
     [[ $(grep -c '^Error:' "$tmp/$fixture.log") -ne 1 ]] ||
     ! grep -Fq "$expected" "$tmp/$fixture.log"; then
    echo "Type congruence negative test $fixture failed for an unrelated reason:" >&2
    cat "$tmp/$fixture.log" >&2; exit 1
  fi
  if [[ $fixture == TypedTypeCongUnrelated ]] &&
     ! grep -Fq 'NeutralEqual ?ctx ?face (NBase FZ) (NBase (FS FZ)) NType' "$tmp/$fixture.log"; then
    echo "Type congruence negative test $fixture did not reject the endpoint equality premise:" >&2
    cat "$tmp/$fixture.log" >&2; exit 1
  fi
done
echo 'Restricted type congruence negative tests passed.'

for fixture in TypedIntervalNonBoolean TypedIntervalWrongPath TypedIntervalFalseFace TypedIntervalScope TypedDependentUnrelated; do
  "$idris" -p fibril --check "$fixture.idr" > "$tmp/$fixture.log" 2>&1 || true
  location='right hand side'
  case $fixture in
    TypedIntervalNonBoolean) expected='Mismatch between: Zero and Var FZ.' ;;
    TypedIntervalWrongPath) expected='Mismatch between: FZ and FS FZ.' ;;
    TypedIntervalFalseFace) expected='Mismatch between: True and False.' ;;
    TypedIntervalScope) expected='Mismatch between: S ?k and 0.'; location='type' ;;
    TypedDependentUnrelated) expected='Mismatch between: FS FZ and FZ.' ;;
  esac
  if ! grep -Fq "While processing $location of bad" "$tmp/$fixture.log" ||
     [[ $(grep -c '^Error:' "$tmp/$fixture.log") -ne 1 ]] ||
     ! grep -Fq "$expected" "$tmp/$fixture.log"; then
    echo "Interval/dependent congruence negative test $fixture failed for an unrelated reason:" >&2
    cat "$tmp/$fixture.log" >&2; exit 1
  fi
done
echo 'Typed interval and dependent abstraction congruence negative tests passed.'

# The interval shapes match IMeetRightOne; rejection must be its face proof,
# not a structural mismatch or a scope error.
fixture=TypedIntervalExcludedMiddle
if "$idris" -p fibril --check "$fixture.idr" > "$tmp/$fixture.log" 2>&1; then
  echo "Expected $fixture to reject Boolean excluded middle on the interval." >&2
  exit 1
fi
if ! grep -Fq 'While processing right hand side of bad' "$tmp/$fixture.log" ||
   [[ $(grep -c '^Error:' "$tmp/$fixture.log") -ne 1 ]] ||
   ! grep -Fq 'Mismatch between: True and False.' "$tmp/$fixture.log" ||
   ! grep -Fq 'bad = IMeetRightOne Refl' "$tmp/$fixture.log" ||
   ! grep -Fq 'TypedIntervalExcludedMiddle:11:21--11:25' "$tmp/$fixture.log"; then
  echo "Interval excluded-middle test failed for an unrelated reason:" >&2
  cat "$tmp/$fixture.log" >&2; exit 1
fi
echo 'Typed interval excluded-middle face-evidence negative test passed.'

for fixture in TypedEqualConvertUnrelated TypedFaceRestrictEscape TypedEqualConvertFace; do
  "$idris" -p fibril --check "$fixture.idr" > "$tmp/$fixture.log" 2>&1 || true
  case $fixture in
    TypedEqualConvertUnrelated) expected='Mismatch between: NType and NPathType' ;;
    TypedFaceRestrictEscape) expected='Mismatch between: True and False.' ;;
    TypedEqualConvertFace) expected='Mismatch between: SBottom and STop.' ;;
  esac
  if ! grep -Fq 'While processing right hand side of bad' "$tmp/$fixture.log" ||
     [[ $(grep -c '^Error:' "$tmp/$fixture.log") -ne 1 ]] ||
     ! grep -Fq "$expected" "$tmp/$fixture.log"; then
    echo "Typed equality conversion/face restriction test $fixture failed:" >&2
    cat "$tmp/$fixture.log" >&2; exit 1
  fi
done
echo 'Typed equality conversion and face restriction negative tests passed.'
for fixture in NeutralEqualRestrictEscape NeutralEqualTransMismatch; do
  "$idris" -p fibril --check "$fixture.idr" > "$tmp/$fixture.log" 2>&1 || true
  case "$fixture" in
    NeutralEqualRestrictEscape) expected='Mismatch between: True and False.' ;;
    NeutralEqualTransMismatch) expected='Mismatch between: FS FZ and FZ.' ;;
  esac
  if [[ $(grep -c '^Error:' "$tmp/$fixture.log") -ne 1 ]] ||
     ! grep -Fq 'While processing right hand side of bad' "$tmp/$fixture.log" ||
     ! grep -Fq "$expected" "$tmp/$fixture.log"; then
    echo "Negative equality closure test $fixture failed for an unrelated reason:" >&2
    cat "$tmp/$fixture.log" >&2; exit 1
  fi
done
echo 'Neutral equality closure negative tests passed.'

"$idris" -p fibril --check TypedCheckerIndexMismatch.idr > "$tmp/typed-checker-index.log" 2>&1 || true
if ! grep -q 'Mismatch between:' "$tmp/typed-checker-index.log" || grep -q 'While processing type of bad' "$tmp/typed-checker-index.log"; then
  echo 'Negative checker index test failed for an unrelated reason:' >&2
  cat "$tmp/typed-checker-index.log" >&2
  exit 1
fi
echo 'Typed checker index mismatch negative test passed.'

"$idris" -p fibril --check ShadowWrongType.idr > "$tmp/shadow-type.log" 2>&1 || true
if ! grep -Fq 'Mismatch between: LUnit and LBool' "$tmp/shadow-type.log"; then
  echo 'Negative shadow typing test failed for an unrelated reason:' >&2
  cat "$tmp/shadow-type.log" >&2
  exit 1
fi
echo 'Shadow typing negative test passed.'
"$idris" -p fibril --check ShadowPathWrongEndpoint.idr > "$tmp/shadow-path.log" 2>&1 || true
if ! grep -Fq 'Mismatch between: True and False' "$tmp/shadow-path.log"; then
  echo 'Negative shadow path endpoint test failed for an unrelated reason:' >&2
  cat "$tmp/shadow-path.log" >&2
  exit 1
fi
echo 'Shadow path endpoint negative test passed.'
for fixture in ShadowFaceEscape ShadowDeclaredWrongEndpoint ShadowDeclaredCapture ShadowErasedReflection; do
  "$idris" -p fibril --check "$fixture.idr" > "$tmp/$fixture.log" 2>&1 || true
  case "$fixture" in
    ShadowFaceEscape) expected='Mismatch between: True and False.' ;;
    ShadowDeclaredWrongEndpoint) expected='Mismatch between: LBoolean True and LRef LHere.' ;;
    ShadowDeclaredCapture) expected='Mismatch between: LBool :: ?context and [].' ;;
    ShadowErasedReflection) expected='Mismatch between: LogicalTerm (shadowContext [BoolTy]) (shadowType BoolTy) and Uses' ;;
  esac
  if ! grep -Fq 'While processing right hand side of bad' "$tmp/$fixture.log" ||
     ! grep -Fq "$expected" "$tmp/$fixture.log" ||
     [[ $(grep -c '^Error:' "$tmp/$fixture.log") -ne 1 ]] ||
     grep -Eq 'Undefined name|While processing type of bad|While processing (type|right hand side) of decls' "$tmp/$fixture.log"; then
    echo "Negative shadow bridge test $fixture failed for an unrelated reason:" >&2
    cat "$tmp/$fixture.log" >&2
    exit 1
  fi
done
echo 'Shadow bridge adversarial tests passed.'
for fixture in ShadowBodyFaceEscape ShadowBodyWrongPath ShadowAbstractWrongEndpoint ShadowBodyTransMismatch; do
  "$idris" -p fibril --check "$fixture.idr" > "$tmp/$fixture.log" 2>&1 || true
  case "$fixture" in
    ShadowBodyFaceEscape) expected='Mismatch between: True and False.' ;;
    ShadowBodyWrongPath) expected='Mismatch between: LHere and LThere LHere.' ;;
    ShadowAbstractWrongEndpoint) expected='Mismatch between: False and True.' ;;
    ShadowBodyTransMismatch) expected='Mismatch between: True and False.' ;;
  esac
  if ! grep -Fq 'While processing right hand side of bad' "$tmp/$fixture.log" ||
     [[ $(grep -c '^Error:' "$tmp/$fixture.log") -ne 1 ]] ||
     ! grep -Fq "$expected" "$tmp/$fixture.log"; then
    echo "Negative shadow body test $fixture failed for an unrelated reason:" >&2
    cat "$tmp/$fixture.log" >&2; exit 1
  fi
  if [[ $fixture == ShadowBodyTransMismatch ]] &&
     { ! grep -Fq 'BodyEqual decls (the (ScopedFace 0) STop) (Embed (LBoolean True)) (NeutralAt (LThere LHere) Zero)' "$tmp/$fixture.log" ||
       ! grep -Fq 'BodyEqual decls (the (ScopedFace 0) STop) (Embed (LBoolean False)) (NeutralAt (LThere LHere) Zero)' "$tmp/$fixture.log"; }; then
    echo 'Transitivity test did not reject its mismatched intermediate endpoints:' >&2
    cat "$tmp/$fixture.log" >&2; exit 1
  fi
done
echo 'Shadow body equality adversarial tests passed.'
"$idris" -p fibril --check ShadowMappedFaceEscape.idr > "$tmp/shadow-mapped-face.log" 2>&1 || true
if ! grep -Fq 'Mismatch between: True and False' "$tmp/shadow-mapped-face.log"; then
  echo 'Negative mapped shadow face test failed for an unrelated reason:' >&2
  cat "$tmp/shadow-mapped-face.log" >&2
  exit 1
fi
echo 'Mapped shadow face escape negative test passed.'
for fixture in ShadowTypedBridgeWrongFace ShadowTypedBridgeWrongIndex; do
  "$idris" -p fibril --check "$fixture.idr" > "$tmp/$fixture.log" 2>&1 || true
  case "$fixture" in
    ShadowTypedBridgeWrongFace) expected='Mismatch between: True and False.' ;;
    ShadowTypedBridgeWrongIndex) expected='Mismatch between: LThere LHere and LHere.' ;;
  esac
  if [[ $(grep -c '^Error:' "$tmp/$fixture.log") -ne 1 ]] ||
     ! grep -Fq 'Error: While processing right hand side of bad.' "$tmp/$fixture.log" ||
     ! grep -Fq "$expected" "$tmp/$fixture.log"; then
    echo "Negative bridge test $fixture failed for an unrelated reason:" >&2
    cat "$tmp/$fixture.log" >&2; exit 1
  fi
  case "$fixture" in
    ShadowTypedBridgeWrongFace)
      if ! grep -Fq 'boundedFaceEntails (the (ScopedFace 1) (SEndpoint FZ True)) (scopedEndpoint (Var FZ) False) = True' "$tmp/$fixture.log"; then
        echo 'Wrong-face fixture did not reject the intended target entailment:' >&2
        cat "$tmp/$fixture.log" >&2; exit 1
      fi ;;
    ShadowTypedBridgeWrongIndex)
      if ! grep -Fq 'DeclaredEndpoint (DeclarePath (LRef (LThere LHere)) (LRef (LThere LHere)) NoPaths)' "$tmp/$fixture.log" ||
         ! grep -Fq 'DeclaredEndpoint (DeclarePath (LRef LHere) (LRef (LThere LHere)) NoPaths)' "$tmp/$fixture.log"; then
        echo 'Wrong-index fixture did not reject the intended source declaration:' >&2
        cat "$tmp/$fixture.log" >&2; exit 1
      fi ;;
  esac
done
echo 'Shadow typed bridge wrong-face and wrong-index tests passed.'
for fixture in StructuralBridgeWrongFace StructuralBridgeWrongSide StructuralBridgeWrongConstructor StructuralBridgeWrongIndex; do
  "$idris" -p fibril --check "$fixture.idr" > "$tmp/$fixture.log" 2>&1 || true
  case "$fixture" in
    StructuralBridgeWrongFace)
      expected='Mismatch between: other and face.'
      detail='simpleFaceEntails other (scopedEndpoint (Var FZ) False)' ;;
    StructuralBridgeWrongSide)
      expected='Mismatch between: True and False.'
      detail='simpleFaceEntails face (scopedEndpoint (Var FZ) True)' ;;
    StructuralBridgeWrongConstructor)
      expected='Mismatch between: DeclaredLeft DeclaredHere ?check and DeclaredRight DeclaredHere Refl.'
      detail='BridgeableEquality (BodyEndpoint (DeclaredLeft DeclaredHere ?check))' ;;
    StructuralBridgeWrongIndex)
      expected='Mismatch between: LThere LHere and LHere.'
      detail='BodyEqual (DeclarePath (LRef (LThere LHere)) (LRef (LThere LHere)) NoPaths)' ;;
  esac
  if [[ $(grep -c '^Error:' "$tmp/$fixture.log") -ne 1 ]] ||
     ! grep -Fq 'Error: While processing right hand side of bad.' "$tmp/$fixture.log" ||
     ! grep -Fq "$expected" "$tmp/$fixture.log" || ! grep -Fq "$detail" "$tmp/$fixture.log"; then
    echo "Structural bridge negative test $fixture failed for an unrelated reason:" >&2
    cat "$tmp/$fixture.log" >&2; exit 1
  fi
  case "$fixture" in
    StructuralBridgeWrongFace|StructuralBridgeWrongSide)
      if ! grep -Fq 'simpleFaceEntails face (scopedEndpoint (Var FZ) False)' "$tmp/$fixture.log" ||
         ! grep -Fq 'bad face other original restriction wrong = BridgeRestrictLeft wrong' "$tmp/$fixture.log"; then
        echo "Structural bridge $fixture did not reject the expected symbolic recertification:" >&2
        cat "$tmp/$fixture.log" >&2; exit 1
      fi ;;
  esac
  if [[ $fixture == StructuralBridgeWrongIndex ]] &&
     ! grep -Fq 'BodyEqual (DeclarePath (LRef LHere) (LRef (LThere LHere)) NoPaths)' "$tmp/$fixture.log"; then
    echo 'Structural bridge wrong index did not reject the requested declaration:' >&2
    cat "$tmp/$fixture.log" >&2; exit 1
  fi
done
echo 'Structural bridge recertification, constructor, and index negative tests passed.'
