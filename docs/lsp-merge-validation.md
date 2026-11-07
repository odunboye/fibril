# LSP foundations: master integration validation

This is merge compatibility evidence, not a new performance measurement or a
usable wire-level Fibril LSP server. Historical JSON observations and their
recorded values/hashes are unchanged. The merged compiler's current behavior is
checked separately from the integrity of those historical observations.

## Historical source epochs

`tools/lsp_evidence_history.py` verifies every recorded digest against actual Git
blob bytes at explicit, immutable revisions, not against the current checkout or
a copied hash manifest. Both normal and sanitizer evidence JSON files must also
remain byte-identical to their preserved recording snapshot.

| Evidence | Input epoch and coverage |
| --- | --- |
| Cost audit | All156 `inputs_sha256` entries at `5ca14f3f4dad4694b049e1fe5167d82e5d462b96`; both JSON files are also preserved there. The recorded `base_commit` remains the earlier `afaf00c4...`, not a claim that newly introduced audit files existed in that earlier commit. |
| Source sharing |148 baseline inputs at `5ca14f3f4dad4694b049e1fe5167d82e5d462b96`;16 files under `tools/fixtures/lsp-source-sharing/` and three candidate helpers (`lsp_source_sharing.py`, `probe_lsp_source_sharing.py`, `test_lsp_source_sharing.py`) at imported snapshot `4278ece473bf361e0fde51cc17422d8857acffb9`. Both JSON files are preserved in that imported snapshot. |
| Workload | All8 `production_source_sha256` entries and both JSON files at `14bc13eb9a517f41853b25ae5f51ba507a9b42f5`. The corpus manifest is additionally checked against the current reproducible corpus. |

The source-sharing observations originally belonged to `840ba8f`; that original
side-branch object need not be present in a clone of merged master. All167 input
blobs and both evidence files were independently compared byte-for-byte between
that original commit and the reachable imported snapshot `4278ece` before using
the latter. This is an **imported contents snapshot**, not a claim that the
measurements executed at the import commit. The helper tests require all three
snapshot revisions to be ancestors of bootstrap merge parent
`cd399d8b2c089fd6a19842b799c203de3ea4afd0`, so publication does not depend on an
unmerged side branch's objects.

The fixed epoch selection has no digest-based fallback, current-file exception,
or skipped changed path. A changed digest or evidence byte fails. Git reads use
the existing bounded, owned-unreaped-anchor whole-buffer/EOF process helper.
A source archive without `.git`, missing Git executable, missing recording object
(including insufficient shallow history), or failed Git read raises explicit
`ProvenanceUnavailable`: historical provenance is **unverified**, not a pass.
No independently authenticated standalone source snapshot is bundled as an
archive fallback.

## Current-source checks

- Alias inversion and all candidate byte-copy checks still read **current**
  baseline/candidate sources. Historical input checks do not replace these.
- Counter-only native instrumentation checks still read the current runtime,
  preserve existing enter/force/allocation/budget contracts, and now explicitly
  cover dynamically discovered `f_nat_case` attribution.
- The current private ModuleCheck clone requires exactly two full runtime-checking
  sites: master's group-aware mutual worker and ordinary module declaration.
  Both original checking calls and success/failure decisions are retained. Missing,
  duplicated or modified sites fail closed; construction counters/diagnostics do
  not introduce another checker, allowance or source rewrite.
- The offline Audit visitor now traverses all four NatCase fields: motive as
  metadata, scrutinee/base/successor function as computational syntax. NatCase
  itself binds nothing. The successor function's actual Lambda quantity extends
  its context, as for all other Lambda syntax; no erased-subtype heuristic is used.
- A separately compiled **current** Audit executable is checked by
  `tools/check_lsp_audit_nat_case.py --audit PATH`. Its two raw closed examples use
  Linear and Unrestricted successor Lambdas, nested erased applications, and
  predecessor references. The checker compares the complete dumped trees, roles,
  quantities and indices, and independently counts descendants against actual
  `coreNodes` (18 each). This is constructor/inventory evidence, not execution of
  the historical LSP workloads.

## Executed merge checks and limits

The initial reconciliation passed build/unit proof compilation and deterministic
regressions,13 structural/5 erased/9 runtime property groups, count5 with27 raw
checks, iteration13, pattern20, and eight focused CLI regressions. Initial raw-test
scope-index elaboration errors were fixed before the passing unit rerun.

The parent's subsequent combined `make -j8 test editor-test handbook` returned
**exit2**, not a pass: handbook navigation contained duplicate IO pages after the
automatic merge. The parent reported all default test groups (including CLI181,
pattern20 and native32) and editor7 passing. That combined failure remains a
failure; its command was not retroactively relabeled successful.

The navigation repair removes17 repeated entries from the later IO section,
retaining all135 already-listed unique page paths, all section headings, the
earlier IO ownership pages, and every later binary/protocol page. The next builder
run exposed two missing navigation entries: the existing master grouped-pattern
plan and this new validation record. Both are registered, bringing the total to137
unique pages. That intermediate builder failure (and dependent handbook-test
errors before assets existed) remains a failed attempt; no document was dropped.

The bounded compatibility follow-up passes audit5, sharing12, provenance/checker6,
oracle8 and workload19. Its first workload19 run failed on the historical runtime
hash before the explicit workload recording epoch was added. The small current
Audit compile and executable NatCase check pass. Handbook generation/local-link
checking and handbook16 are rerun separately for the navigation repair; they do
not constitute a rerun of the failed combined command.

No historical JSON matrix, framing/lifecycle performance matrix or new sanitizer
matrix was executed by this follow-up. No production core, runtime, source
lowering, capability gate, work allowance or public API changed during the
compatibility repair. Parent review and final publication remain separate gates.

## Parent final acceptance of the resolved merge

The parent independently reran the combined
`make -j8 test editor-test handbook` command after the compatibility/navigation
repairs: **exit0**. This later success does not change the earlier exit2 result.
The unit/proof/property phase passed; suite groups passed: CLI181, pattern20,
native32, pairs8, bytes/UTF-8 native7, binary source13, raw binary bridge1,
count5 (including27 raw checks and the new checked NatCase denial cases),
iteration13, scalability9, numeric6, oracle8, JSON iteration7, framing14,
interactive CLI9, editor7 and handbook16.

Separate parent executions on the resolved merge also passed:

- `make -j8 io-test`: all configured hosted/native IO targets, including the
  hosted checks and binary bridge/interactive differential paths.
- ASan/UBSan raw console19, resource25 and binary bridge1 suites.
- ASan/UBSan count5 and iteration13 suites, including the merged count paths.
- Typed lifecycle5 normally and with ASan/UBSan. The two current records are
  exactly equal with133 rows. These are current executions, not a replacement
  for the immutable historical measurement records.
- Offline audit5, source-sharing/harness12, historical provenance/checker6,
  workload19 and byte-span model9. Model checks remain models, not implemented
  byte-span operations.

Three independent read-only reviews accepted, respectively, the reducer/count
reconciliation, complementary native/frontend/admission merge, and14-file offline
compatibility repair. They inspected source/patches; parent executions are not
attributed to those reviewers. No runtime limit, admission exception, erased/
dormant capability bypass or production LSP claim was introduced.

The merge has parents master `482c93ab67a552dc0b554e237e7607985276d932` and
bootstrap `cd399d8b2c089fd6a19842b799c203de3ea4afd0`. Main-worktree local Makefile
edits and untracked recursion-tour/agent files are not part of the merge; they
must remain preserved during the final fast-forward publication. No remote push
is implied.

## Subsequent all-LSP integration with region-enabled master

The later merge combines master `76a85031b53ae46ca783af3dca610aa0f2ee3a2a`
with consolidated `feature/lsp` tip `bdcbaadf9cd167614fd44c5e4050a7bdbf7d4a2d`.
It includes the usable Python server and all four original LSP worker-branch
histories. The separate [consolidation record](lsp-consolidation.md) describes
that earlier feature-branch checkpoint; it is not this merge's validation log.

Master's Core/runtime/stdlib files are byte-identical to `76a8503`, retaining
recursion and scoped-region support. Python server/test files are byte-identical
to the incoming branch and original `9e87c0d`. Navigation merges retain both
master's grouped-pattern/synthetic-scrutinee handling and Python LSP module
qualifier callbacks, shared destination/origin ranges and reference metadata.
The current offline inventory additionally handles WithRegion's two fields in
the same context; its complete11-node raw regression supplements the existing
NatCase18-node checks. Historical evidence JSON and epoch contracts are unchanged.

The parent independently ran `make -j8 test editor-test handbook`: **exit0**.
The unit/proof/property phase and all configured suites passed: CLI181, pattern20,
native32, pair8, byte/UTF-8 native7, binary source13, bridge1, count5, iteration13,
scalability9, numeric6, oracle8, JSON iteration7, framing14, interactive CLI9,
Python LSP29, editor7 and handbook16. Separate parent runs passed region6
(including its native sanitizer coverage), audit5, sharing12, provenance/checker7,
workload19 and the full `make -j8 io-test` target. Raw console19, resource25 and
binary bridge1 also passed under ASan/UBSan.

An independent read-only reviewer accepted the navigation, compatibility,
WithRegion inventory and documentation union after inspecting16 bounded
per-parent conflict diffs. That review executed no tests; the parent owns the
executed results above. The worker also compiled and ran the actual current
Audit checker against NatCase and WithRegion examples. Its two initial direct
standalone compiler attempts failed on missing transitive YAML/parser packages;
the later private-package build passed. A pre-registration book completeness
check also failed on missing `docs/regions.md`, which is now registered. These
failed attempts remain failed, not retroactively passing commands.

The Python LSP is now included in master, but the Fibril-written wire server is
still undelivered. No new byte-span API, budget increase, capability relaxation,
historical performance rerun, source-worktree deletion or remote push is implied.
Local main-worktree Makefile additions and untracked files remain outside this
merge and must be preserved during publication.
