# Consolidated LSP worktrees

This is the historical `feature/lsp` consolidation record, before its integration
with newer master. The Python server is now included alongside those newer master
features; see [current LSP status](lsp-status.md). Test counts below describe that
earlier checkpoint, not a rerun on the current compiler. Current provenance checks
retain master's imported `4278ece` source-sharing epoch and bootstrap ancestry;
the original `840ba8f` is also reachable through the incoming worker history.

## Scope at that checkpoint

The `feature/lsp` branch retains its Python LSP implementation and directly merges
all four requested worker branches, preserving their original histories:

| Source worktree | Branch | Merged tip |
| --- | --- | --- |
| `fibril-lsp-cost-audit` | `feature/lsp-cost-audit` | `c280891` |
| `fibril-lsp-lifecycle` | `feature/lsp-lifecycle` | `cdf7886` |
| `fibril-lsp-source-sharing` | `feature/lsp-source-sharing` | `f3d4a14` |
| `fibril-lsp-workload` | `feature/lsp-workload` | `10fc689` |

This consolidates these branches into the existing `fibril-lsp` checkout. It does
not merge unrelated worktrees or all newer master features, change master, delete
branches/worktrees, or imply a remote push.

## What runs

The usable language server remains the [Python LSP](lsp.md). Its server and test
sources are unchanged from `9e87c0d`; compiler-backed checking/navigation now coexist
with the imported checked binary-IO, frame, JSON/lifecycle and audit foundations.
The Fibril lifecycle is a typed-event diagnostic, not a wire decoder/server. The
64-byte JSON diagnostic and source-sharing candidates remain limited; larger JSON,
general headers, source-level wire dispatch and composed admission are not solved.

Core/runtime/stdlib code is unchanged from the merged source-sharing lane. Merge
resolutions retain both Makefile target sets, private test-prefix staging, Python
LSP tests, binary tests and documentation. No budget or capability gate is relaxed.

## Validation and historical measurements

The combined `make -j8 test editor-test handbook` command passed on the combined
code: unit/proof/property phase, CLI163, native19, pairs8, bytes7, binary source13,
bridge1, count5, iteration13, scalability9, numeric6, oracle8, JSON iteration7,
framing14, interactive CLI9, Python LSP29, editor7 and handbook16.

Historical cost/source-sharing checks initially failed because they compared the
combined compiler's source files to pre-consolidation fingerprints. Recorded
measurements and JSON files are unchanged. The repaired checks verify actual Git
blob bytes at explicit epochs: baseline/cost `5ca14f3`, original sharing `840ba8f`,
and workload `14bc13e`. Unlike the master import, the original sharing recording is
now an ancestor through the directly merged branch. All epochs must be ancestors
of merged source-sharing tip `f3d4a14`. Missing Git/history or source archives fail
explicitly rather than claiming verified provenance.

Offline provenance5, audit5, sharing/harness12 and workload19 checks pass after
that repair. Current alias inversion, candidate byte copies and instrumentation
checks still inspect current sources. These integrity checks do not rerun or
relabel the historical performance matrices. The earlier source-sharing agent
timeout remains a failed run, as documented in its [record](lsp-source-sharing.md).

The independent master merge and its newer recursion reconciliation remain on
master; this consolidation does not claim to reproduce that different tree or
its measurements.
