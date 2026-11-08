# Independent build-performance review

Revision reviewed: `c8caac2`, including the existing uncommitted investigation in
`docs/build-performance.md`. This review does not change compiler behavior.

## Conclusion

The strongest evidence points to **Idris 2's termination analysis of
`Fibril.Elaboration.Expression`**, aggravated by allocation and garbage collection.
This is the host compiler checking Fibril's implementation, not Fibril running its
own termination checker on a user's program.

The evidence explains a multi-minute build stall, but a completed, controlled
30–40 minute build has not yet been recorded here. Do not interpret a partial
profile as a precise attribution of the entire reported build time.

## Independent observations

A pre-existing baseline was already running when this review began; no competing
build was launched, and that process was not stopped or modified.

- Command: `tools/profile_build.py --cache build/build-profiles/full-baseline/cache --timing 3`.
- Compiler: pinned Idris revision `74b33730b6fea649b15e8d01ab099df9effcc7a0`, Chez backend.
- Log: `build/build-profiles/20261108T164152928373Z/compiler.log`.
- At inspection: over 12 minutes elapsed, approximately one CPU core saturated,
  and about 8.3 GiB resident memory. Machine: 24 GiB RAM, 14 logical CPUs.
- The first 97 completed module elaboration timings summed to **72.837 seconds**.
  Expression was the next unfinished module. Module timings do not include every
  build cost and should not be equated with end-to-end elapsed time.
- Largest completed modules: ShadowCommon **41.865 s**, CommonAdmission **5.834 s**,
  NormalForm **3.542 s**, ShadowPath **3.032 s**. ShadowCommon's totality phase
  alone took **35.928 s**; CommonAdmission's took **3.168 s**. Thus termination
  checking is a measured secondary cost in the proof stack too.
- A two-second macOS `sample` of the active compiler collected 182 main-thread
  samples; **140 were underneath `S_do_gc`**. This is a short-window observation,
  not a whole-build GC percentage. Native sampling did not resolve Scheme-level
  functions, so it cannot independently identify the executing Idris function.
- System memory pressure did not indicate an acute system-wide memory shortage
  at that observation. Large allocation/collection overhead is not the same as
  proof that the machine is swapping.

The live log's last visible entries are Expression RHS/case-tree/coverage checks.
Output is buffered; the last line alone is not proof of the current phase.
The earlier controlled phase-isolation evidence supplies the stronger diagnosis:

- Unmodified Expression was deliberately stopped after at least **261.07 CPU s**.
- A disposable copy changing `%default total` to `%default covering` completed
  module elaboration in **1.623 s**, including **1.355 s** processing declarations,
  **0.000 s** reported totality checking, and **0.085 s** compiling definitions.
  An independent source comparison confirmed that the diagnostic copy differs
  only in the default totality directive.
- This is strong evidence that termination checking dominates this module. It is
  **not** a valid production fix: it removes a guarantee.

## Why this source stresses the checker

`src/Fibril/Elaboration/Expression.idr:32` specifies `%default total`.
Its mutual block begins at line 248 and extends through approximately line 1483.
The existing lexical graph identifies 44 declarations and an approximately
30-function recursive component. Lexical counts are not the generated checker
call graph: implicit parameters, case blocks and higher-order calls matter too.

Important paths include `elaborateInWithGlobals`, `elaborateExpectedGlobals`
(line 560), data-case traversal, implicit applications, and equation bodies.
The catch-all helpers at lines 474, 506 and 527 pass many context, term and
branch arguments while calling back into central elaboration. A syntactically
small language feature can add many compositions to a recursive size-change
problem; source line count is not a reliable predictor of checking cost.

The pinned compiler's `Idris/ProcessIdr.idr:388–396` explicitly orders processing
of declarations, totality checking, then definition compilation. Its installed
`Core/Termination/SizeChange.idr` provides a concrete mechanism:

- `composeChange` multiplies argument-change matrices.
- `composeGraph` composes matrices and concatenates diagnostic call paths.
- `preCompose`/`postCompose` create candidate graphs and deduplicate by matrix.
- `addGraph`/`transitiveClosure` repeatedly extend the graph to closure.
- `findLoops` checks idempotent self-call graphs for descending arguments.

Many recursive paths and argument relationships can produce many distinct
matrices and temporary objects. This is consistent with high CPU use, heap
growth, and the observed GC-heavy sample. Exact matrix counts and per-function
costs remain unmeasured; instrumenting the host compiler would establish those.

## Recommendations, in order

1. **Finish one controlled baseline.** Retain wall time, peak RSS, exit status,
   module/totality timing and executable-generation timing. Repeat unchanged and
   then compare leaf-edit and foundational-edit rebuilds. Keep competing compiler
   processes out of the measurements.
2. **Reduce the actual recursive checking problem.** Extract helpers that do not
   call back into elaboration; aim to reduce recursive edges and independent
   argument relationships. Merely moving the same cycle across files does not
   solve it. Keep totality guarantees and acceptance/rejection regression tests.
3. **Treat simple refactors as experiments, not established fixes.** Existing
   disposable runs for bundling, local helpers, inline hints and dispatch inlining
   all ended with exit 143 after roughly 182–313 seconds. They establish neither
   successful compilation nor a speedup. In particular, bundling arguments is not
   an evidence-backed quick fix yet.
4. **Consider a bounded host-compiler investigation.** Count closure candidates,
   unique matrices, worklist size and diagnostic path lengths. Compare another
   Idris revision in an isolated cache with the full regression suite. Do not
   change the project pin on the assumption that a newer compiler fixes this.
5. **Preserve incremental caches.** Avoid routine `make clean`; distinguish real
   dependency changes from timestamp-only invalidation. Benchmark `-Xcheck-hashes`
   separately and key persistent caches by compiler/dependency versions.
6. **Remove repeated executable generation from test staging.** A separate library
   package can be installed for unit tests without rebuilding the CLI. Preserve
   private test installation and dependency filtering. Measure this independently
   of totality analysis.
7. **Locate the regression window if earlier builds were fast.** Recent changes
   include general recursive data (`1487aca`), multi-field cases (`0b5931a`),
   single-constructor cases (`8440e2d`), and recursive catch-all clauses
   (`b22470d`). The last changed Expression by 124 additions and 54 deletions.
   These are bisect candidates, not proven causes. Compare isolated worktrees,
   the same host compiler, and equivalent cache states; preserve current changes.
8. **Only then optimize secondary costs.** ShadowCommon is a measured secondary
   hotspot. Audit unnecessarily transparent `public export` bodies carefully;
   proof/type-level reduction may require them. Incremental Chez may help CLI
   generation but cannot fix Expression totality checking.

## What is unlikely to solve the reported delay

- `make -j`: the principal recipe invokes one Idris build; it does not parallelize
  the host compiler's closure computation.
- Removing the 26 modules outside Main's import closure: the earlier sample
  attributed only about 5.6 seconds of module elaboration to them. Main imports
  the experimental cubical frontend (`src/Main.idr:4`), so the logical stack is
  not simply unused validation code that can all be dropped from CLI builds.
- Blaming the approximately 25 MiB NormalForm interface alone: measured checking
  was only approximately 3.5–4.2 seconds in the available runs.
- Tuning Chez's final native compilation first: the earlier existing-generated-
  Scheme experiment took about 4.15 seconds. That excludes Idris code generation
  and does not validate the current source snapshot.
- Changing to `covering`/`partial`, inserting unchecked totality assertions, or
  imposing arbitrary fuel: these can remove guarantees or change behavior.

## Additional test-staging concern

The local `~/.local/bin/idris2` Pack shim unconditionally resets
`IDRIS2_PACKAGE_PATH`, `IDRIS2_LIBS`, and `IDRIS2_DATA`. This can override the
external-package filtering and private-library selection established by
`tools/test_units.py:45–59` when the script uses its default compiler command.
Resolve the pinned compiler executable directly (as the profiler does) before
applying the private staging environment. This is a test-isolation/reproducibility
concern, not an established explanation for the 30–40 minute build. No change to
the shim or test script was made during this review.

## Scope and limits

No production source, build recipe, package definition or existing investigation
was modified. No full regression suite was run because this is a read-only
performance evaluation. The already-running full baseline was left running.
The existing profiler is useful for compiler-phase timing but does not currently
record peak memory, source-tree dirty state, CPU time, or durable interrupted-run
summaries. Add these before treating its output as a complete benchmark record.
