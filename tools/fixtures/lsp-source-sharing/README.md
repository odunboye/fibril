# Two-alias source-sharing CANDIDATE

Private explicit source root, **not** the production examples/CLI root. Logical
module identities (`Protocol.Frame`, `Protocol.JSON`, `LSP`, etc.) are unchanged.
Only two source edits differ from their baseline files:

- Frame: one unrestricted lexical `sharedEqualString` function value, with the
  original two linear String arguments; replace `equalString` references.
- JSON: one unrestricted lexical `sharedOrBool` function value, with the original
  two linear Bool arguments; replace `orBool` references. The existing `sameText`
  alias of `equalString` is unchanged.

All other files are byte copies of existing binary-frame, json-iteration,
lsp-lifecycle or lsp-cost-audit fixtures. Original files and accepted audit hash
provenance remain untouched. Hosted.idr/SourceHarness.c are the existing test
adapters, not executing JSON grammars. No Python state handler or C parser exists
in this candidate. No policy, grammar, cap, depth/count allowance, primitive,
runtime or source API is changed.

`tools/probe_lsp_source_sharing.py` explicitly selects this root and reuses the
full 120-case JSON matrix and 14 framing regressions, including their actual
source checking/emission/execution. `tools/lsp_source_sharing.py` inverses only
introduced lexical reference aliases to demand exact baseline source, then
expands exactly the introduced binder in the actual checked syntax, with proper
de Bruijn binder removal and outer-index shifts. Imported helper RHSs must be
closed and identical; types, linear argument quantities and unrestricted value
binder are checked. All other constructors/scalars must exactly match. This is
**accepted-source preservation**, not a full grammar formal proof.

EchoThenTyped/JSONThenTyped remain admission-only independent fixed demands.
`echoFrame` is opaque echo, **not** a body callback. There is no frame-body-to-JSON
routing, wire decoder, typed event composition, combined savings or LSP delivery
claim. Remaining construction/node refusals are recorded as blockers.

See `docs/lsp-source-sharing.md` for measured results and reproduction.
