# OFFLINE LSP cost/admission audit fixtures

These are private typed test/admission fixtures, not public APIs or wire LSP.
No core, runtime, framer, parser, primitive, cap or loop allowance is changed.
See `docs/lsp-cost-audit.md` for measurements, limitations and reproduction.

- `Audit.idr`: private syntax inventory using the actual checked project term.
  Mirrors `coreNodes`, including descriptor/index/branch list cells, and separates
  literal payload from nominal-key payload. Annotated types/motives and existing
  erased-inference/quantity rules label roles; it does not rewrite any term.
- `EqualString.fib`, `OrBool.fib`: pure helper-alias entries. The inventory
  fingerprints their actual imported RHS separately from the main-binding wrapper
  and counts those same syntax fragments in larger entries, without rewriting them.
- `FullIdFour.fib`: recreated four-event typed handshake with the **full** ID
  observer (numeric `1`, then decoded string `1`). This is not the control-only
  episode and not a wire-ID decoder. Native admission failure is a blocker.
- `EchoThenTyped.fib`: actual closed canonical echo followed by a fixed typed
  full observation length demand. The typed request is independent of the frame.
- `JSONThenTyped.fib`: fixed buffered `[]` parsing followed by an independent
  fixed typed request and **control-only state** demand. Not full-ID evidence.
- `EchoJSONThenTyped.fib`: sequential echo then that fixed-buffer probe. **Not**
  frame-body routing: `echoFrame` offers no body continuation, and JSON only
  produces raw-lexeme tokens, not typed events. Source-construction refusal is
  retained as a blocker, not a successful checked/admitted composition.

The last three are ADMISSION PROBES ONLY; none is executed as a protocol pipeline.
No test substitutes a control projection for the full-ID four-event fixture.

`tools/probe_lsp_cost_audit.py` copies unchanged imported modules into a private
root, checks actual entries, inventories accepted terms, and attempts binary
emission without exceptions. Only the existing Read65 diagnostic is executed,
with the same four complete 64-byte controls from the workload baseline. Its
private attributed runtime and un-attributed observer must agree on all existing
metrics and exact oracle output. `tools/lsp_cost_instrument.py` adds counters,
never extra forcing/decisions/charges. All launches reuse `run_process` from the
fixed workload probe: bounded foreground, whole buffer + EOF, not live stdin.

Repeated subtree **shapes** omit values, quantities, variable indices and names.
A separate syntax fingerprint includes every scalar constructor field (variable
indices, quantities, literal contents, nominal keys), but not the surrounding
context/free-variable meanings. Both inventories' counts overlap and are not safe
CSE opportunities, measured savings, erasure results or an admission proposal.
Lexical helper/source changes
would require separate review and real remeasurement of their closed terms.
