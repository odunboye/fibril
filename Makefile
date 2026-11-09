PACK ?= pack
IDRIS2 ?= '$(CURDIR)/tools/fibril_idris.py'
TEST_JOBS ?= 4
# Optional worker profile only; ordinary builds do not link SQLite.
SQLITE_CFLAGS ?= $(shell pkg-config --cflags sqlite3 2>/dev/null)
SQLITE_LIBS ?= $(shell pkg-config --libs sqlite3 2>/dev/null || echo -lsqlite3)

.PHONY: std-test prelude prelude-check build unit-test test io-test io-hosted-test io-runtime-test io-resource-runtime-test io-resource-emitter-test io-emitter-test io-interactive-test io-binary-test io-binary-bench io-cli-test native-test region-test native-pair-test bytes-native-test binary-source-test binary-iteration-test binary-count-test binary-runtime-test binary-scale-test binary-number-test binary-number-bench json-oracle-test json-sharing-probe json-iteration-test lsp-lifecycle-test framing-test header-iteration-test editor-test lsp-test examples bench bench-smoke composed-bench python-embed-test docs handbook serve-docs clean cubical-source-test
.PHONY: host-compiler-test native-embedding-test native-embedding-generated-test binary-embedding-test binary-embedding-generated-test queue-test worker-test worker-demo
prelude:
	python3 tools/embed_prelude.py

prelude-check:
	python3 tools/embed_prelude.py --check

build: prelude-check javascript-runtime-check
	$(PACK) install-deps fibril
	PACK="$(PACK)" $(IDRIS2) --build fibril.ipkg

host-compiler-test:
	PACK="$(PACK)" python3 tools/test_host_compiler.py

# Trusted host boundary: standalone C fixtures, no compiler bootstrap required.
native-embedding-test:
	CC="$(CC)" python3 tools/test_native_embedding.py

native-embedding-generated-test: build
	CC="$(CC)" python3 tools/test_native_embedding_generated.py

# Optional POSIX/SQLite host adapter; not linked into the compiler/runtime by default.
queue-test:
	CC="$(CC)" python3 tools/test_queue.py

worker-test: build
	CC="$(CC)" SQLITE_CFLAGS="$(SQLITE_CFLAGS)" SQLITE_LIBS="$(SQLITE_LIBS)" python3 tools/test_worker.py

# Local EOF-framed demonstration, not an authenticated network server.
worker-demo: build
	mkdir -p build/worker
	./build/exec/fibril emit-c-binary --source-dir examples/modules/queue-worker examples/modules/queue-worker/Main.fib > build/worker/validator.c
	$(CC) $(CFLAGS) -std=c11 -Wall -Wextra -Werror -DFIBRIL_EMBED_ONLY $(SQLITE_CFLAGS) -I runtime/native build/worker/validator.c examples/native/queue_worker.c runtime/native/fibril_worker.c runtime/native/fibril_queue.c runtime/native/fibril_binary_runtime.c $(SQLITE_LIBS) -o build/worker/queue-worker

binary-embedding-test:
	CC="$(CC)" python3 tools/test_binary_embedding.py

binary-embedding-generated-test: build
	CC="$(CC)" python3 tools/test_binary_embedding_generated.py

cubical-source-test: build
	python3 tools/test_cubical_frontend.py
	python3 tools/test_cubical_application.py

# A private package prefix avoids stale/shared Fibril installs across worktrees.
# CLI-consuming suites wait for this staging phase.
unit-test: build
	PACK="$(PACK)" IDRIS2="$(IDRIS2)" python3 tools/test_units.py

# Stage once before suites run concurrently; TEST_JOBS=1 is the serial baseline.
test: build
	PACK="$(PACK)" IDRIS2="$(IDRIS2)" CC="$(CC)" python3 tools/test_all.py --jobs $(TEST_JOBS)

# Each suite builds in its own temporary directory, safe with make -j8.
io-test: io-hosted-test io-runtime-test io-resource-runtime-test io-resource-emitter-test io-emitter-test io-interactive-test io-binary-test

io-binary-test:
	IDRIS2="$(IDRIS2)" CC="$(CC)" python3 tools/test_io_binary.py

# Measurement only: validates output but never asserts timing thresholds.
io-binary-bench:
	IDRIS2="$(IDRIS2)" CC="$(CC)" python3 tools/bench_binary.py

# Offline shared-graph admission and execution measurements, no timing gates.
composed-bench: build
	PACK="$(PACK)" IDRIS2="$(IDRIS2)" CC="$(CC)" python3 tools/probe_composed.py

.PHONY: json-evaluation-profile
json-evaluation-profile: build
	CC="$(CC)" python3 tools/probe_json_evaluation.py --output build/benchmarks/json-evaluation.json

.PHONY: construction-audit
construction-audit: build
	PACK="$(PACK)" IDRIS2="$(IDRIS2)" python3 tools/probe_construction.py --output build/benchmarks/construction.json

io-hosted-test:
	IDRIS2="$(IDRIS2)" python3 tools/test_io_hosted.py

io-runtime-test:
	CC="$(CC)" python3 tools/test_io_native_runtime.py

io-resource-runtime-test:
	CC="$(CC)" python3 tools/test_io_native_resources.py

io-resource-emitter-test:
	IDRIS2="$(IDRIS2)" CC="$(CC)" python3 tools/test_io_resource_emitter.py

io-emitter-test:
	IDRIS2="$(IDRIS2)" CC="$(CC)" python3 tools/test_io_emitter.py

io-interactive-test:
	IDRIS2="$(IDRIS2)" CC="$(CC)" python3 tools/test_io_interactive.py

io-cli-test: unit-test
	CC="$(CC)" python3 tools/test_io_cli.py

region-test: unit-test
	CC="$(CC)" python3 tools/test_region.py

native-test: unit-test
	CC="$(CC)" python3 tools/test_native.py
	IDRIS2="$(IDRIS2)" CC="$(CC)" python3 tools/test_native_pairs.py
	CC="$(CC)" python3 tools/test_bytes_native.py
	CC="$(CC)" python3 tools/test_native_words.py

std-test: unit-test
	CC="$(CC)" python3 tools/test_std.py

native-pair-test: unit-test
	IDRIS2="$(IDRIS2)" CC="$(CC)" python3 tools/test_native_pairs.py

binary-scale-test: unit-test
	CC="$(CC)" python3 tools/test_binary_scalability.py

json-oracle-test:
	python3 tools/test_json_oracle.py

json-sharing-probe: build
	CC="$(CC)" python3 tools/observe_json_combined.py

# Source-only 64-byte diagnostic, with independent oracle and private observers.
json-iteration-test: build
	IDRIS2="$(IDRIS2)" CC="$(CC)" python3 tools/test_json_iteration.py

# Typed-event source-only lifecycle prototype, not a wire LSP implementation.
lsp-lifecycle-test: build
	IDRIS2="$(IDRIS2)" CC="$(CC)" python3 tools/test_lsp_lifecycle.py

binary-number-test: unit-test
	python3 tools/test_binary_numbers.py

binary-number-bench: unit-test
	CC="$(CC)" python3 tools/bench_binary_numbers.py

framing-test: unit-test
	CC="$(CC)" python3 tools/test_framing.py

# Diagnostic source/observer coverage, not generalized framing acceptance.
header-iteration-test: build
	CC="$(CC)" python3 tools/test_header_iteration.py

# Builds/installs only the worktree package into build/test-prefix.
binary-count-test: build
	IDRIS2="$(IDRIS2)" CC="$(CC)" python3 tools/test_binary_count.py

binary-iteration-test: binary-count-test
	IDRIS2="$(IDRIS2)" CC="$(CC)" python3 tools/test_binary_iteration.py

binary-runtime-test:
	CC="$(CC)" python3 tools/test_binary_native.py

binary-source-test: unit-test
	CC="$(CC)" python3 tools/test_binary_source.py
	CC="$(CC)" python3 tools/test_binary_native.py

bytes-native-test: unit-test
	CC="$(CC)" python3 tools/test_bytes_native.py

examples: build
	$(PACK) run fibril-examples
	./build/exec/fibril manifest examples/manifests/mailer/fibril.yaml
	./build/exec/fibril manifest examples/manifests/email-core/fibril.yaml
	./build/exec/fibril check --package examples/packages/mailer/fibril.yaml
	./build/exec/fibril run --package examples/packages/mailer/fibril.yaml
	./build/exec/fibril check --package examples/packages/boolean-library/fibril.yaml
	./build/exec/fibril test --package examples/packages/boolean-library/fibril.yaml
	./build/exec/fibril check --package examples/packages/sum-library/fibril.yaml
	./build/exec/fibril test --package examples/packages/sum-library/fibril.yaml
	./build/exec/fibril run --package examples/packages/sum-client/fibril.yaml
	./build/exec/fibril check --package test/fixtures/packages/request-api/fibril.yaml
	./build/exec/fibril test --package test/fixtures/packages/request-api/fibril.yaml
	./build/exec/fibril check --source-dir examples/modules/binary-frame examples/modules/binary-frame/Main.fib
	./build/exec/fibril check --source-dir examples/modules/binary-frame examples/modules/binary-frame/Two.fib
	./build/exec/fibril check examples/core/binary-echo.fib
	./build/exec/fibril check examples/core/binary-echo-loop.fib
	./build/exec/fibril run examples/core/utf8-bytes.fib
	./build/exec/fibril run examples/core/bytes-ranges.fib
	./build/exec/fibril run examples/core/bytes-native.fib
	./build/exec/fibril check examples/core/bytes-pure.fib
	./build/exec/fibril eval examples/core/bytes-pure.fib
	./build/exec/fibril check examples/core/identity.fib
	./build/exec/fibril check examples/core/identity-unicode.fib
	./build/exec/fibril check --erased examples/core/identity-type.fib
	./build/exec/fibril check examples/core/universe-lift.fib
	./build/exec/fibril eval examples/core/evaluate-identity.fib
	./build/exec/fibril check examples/core/identity-annotated.fib
	./build/exec/fibril eval examples/core/local-identity.fib
	./build/exec/fibril eval examples/core/unit.fib
	./build/exec/fibril eval examples/core/word-arithmetic.fib
	./build/exec/fibril run examples/core/word-native.fib
	./build/exec/fibril run examples/core/word-division.fib
	./build/exec/fibril run examples/core/bytes-equal.fib
	./build/exec/fibril eval examples/core/consume-unit.fib
	./build/exec/fibril eval examples/core/boolean.fib
	./build/exec/fibril eval examples/core/branch-permissions.fib
	./build/exec/fibril eval examples/core/declarations.fib
	./build/exec/fibril eval examples/core/declarations-polymorphic.fib
	./build/exec/fibril check examples/core/hello-world.fib
	./build/exec/fibril run examples/core/hello-world.fib
	./build/exec/fibril run examples/core/javascript.fib
	./build/exec/fibril run examples/core/embedded.fib
	./build/exec/fibril run examples/core/console-sequence.fib
	./build/exec/fibril eval examples/core/string-identity.fib
	./build/exec/fibril run examples/core/console-expressions.fib
	./build/exec/fibril run examples/core/io-functions.fib
	./build/exec/fibril run examples/core/io-map.fib
	./build/exec/fibril run examples/core/do-bindings.fib
	./build/exec/fibril run examples/core/do-let.fib
	./build/exec/fibril run examples/core/do-result.fib
	./build/exec/fibril run examples/core/string-append.fib
	./build/exec/fibril run examples/core/string-equal.fib
	./build/exec/fibril run examples/core/boolean-library.fib
	./build/exec/fibril module-graph examples/modules/graph examples/modules/graph/Main.fib
	./build/exec/fibril check --source-dir examples/modules/checked examples/modules/checked/Main.fib
	./build/exec/fibril eval --source-dir examples/modules/checked examples/modules/checked/Main.fib
	./build/exec/fibril run --source-dir examples/modules/checked examples/modules/checked/Main.fib
	./build/exec/fibril run --source-dir examples/modules/operations examples/modules/operations/Main.fib
	./build/exec/fibril run --source-dir examples/modules/records examples/modules/records/Main.fib
	./build/exec/fibril run --source-dir examples/modules/records examples/modules/records/Patterns.fib
	./build/exec/fibril run --source-dir examples/modules/record-parameters examples/modules/record-parameters/Main.fib
	./build/exec/fibril run --source-dir examples/modules/record-projections examples/modules/record-projections/Main.fib
	./build/exec/fibril run --source-dir examples/modules/wider-records examples/modules/wider-records/Main.fib
	./build/exec/fibril run --source-dir examples/modules/wider-records examples/modules/wider-records/ManyFields.fib
	./build/exec/fibril run --source-dir examples/modules/singleton-records examples/modules/singleton-records/Main.fib
	./build/exec/fibril run --source-dir examples/modules/singleton-records examples/modules/singleton-records/Dependent.fib
	./build/exec/fibril run --source-dir examples/modules/interfaces examples/modules/interfaces/Main.fib
	./build/exec/fibril run --source-dir examples/modules/interface-blocks examples/modules/interface-blocks/Main.fib
	./build/exec/fibril run --source-dir examples/modules/constraints examples/modules/constraints/Main.fib
	./build/exec/fibril run --source-dir examples/modules/inferred-constraints examples/modules/inferred-constraints/Main.fib
	./build/exec/fibril run --source-dir examples/modules/operators examples/modules/operators/Main.fib
	./build/exec/fibril run --source-dir examples/modules/visible-implementations examples/modules/visible-implementations/Main.fib
	./build/exec/fibril run --source-dir examples/modules/infix examples/modules/infix/Main.fib
	./build/exec/fibril run --source-dir examples/modules/implementation-factories examples/modules/implementation-factories/Main.fib
	./build/exec/fibril run --source-dir examples/modules/data examples/modules/data/Main.fib
	./build/exec/fibril run --source-dir examples/modules/bare-type examples/modules/bare-type/Main.fib
	./build/exec/fibril run --source-dir examples/modules/function-equations examples/modules/function-equations/Main.fib
	./build/exec/fibril run --source-dir examples/modules/implicit-arguments examples/modules/implicit-arguments/Main.fib
	./build/exec/fibril run --source-dir examples/modules/implicit-constraints examples/modules/implicit-constraints/Main.fib
	./build/exec/fibril run --source-dir examples/modules/implicit-constructors examples/modules/implicit-constructors/Main.fib
	./build/exec/fibril run --source-dir examples/modules/nat-recursion examples/modules/nat-recursion/Main.fib
	./build/exec/fibril run --source-dir examples/modules/nat-predecessor examples/modules/nat-predecessor/Main.fib
	./build/exec/fibril run --source-dir examples/modules/recursive-equations examples/modules/recursive-equations/Main.fib
	./build/exec/fibril run --source-dir examples/modules/recursive-render examples/modules/recursive-render/Main.fib
	./build/exec/fibril run --source-dir examples/modules/recursive-data examples/modules/recursive-data/Main.fib
	./build/exec/fibril run --source-dir examples/modules/recursive-list examples/modules/recursive-list/Main.fib
	./build/exec/fibril run --source-dir examples/modules/indexed-vect --fuel 4096 examples/modules/indexed-vect/Main.fib
	./build/exec/fibril run --source-dir examples/modules/index-refinement examples/modules/index-refinement/Main.fib
	./build/exec/fibril run --source-dir examples/modules/mutual-data examples/modules/mutual-data/Main.fib
	./build/exec/fibril run --source-dir examples/modules/nested-data examples/modules/nested-data/Main.fib
	./build/exec/fibril run --source-dir examples/modules/linear-accumulator examples/modules/linear-accumulator/Main.fib
	./build/exec/fibril run --source-dir examples/modules/linear-accumulator examples/modules/linear-accumulator/Decorated.fib
	./build/exec/fibril run --source-dir examples/modules/linear-accumulator examples/modules/linear-accumulator/StringAccumulator.fib
	./build/exec/fibril run --source-dir examples/modules/linear-accumulator examples/modules/linear-accumulator/Matches.fib
	./build/exec/fibril run --source-dir examples/modules/linear-accumulator examples/modules/linear-accumulator/AccumulatorFirst.fib
	./build/exec/fibril run --source-dir examples/modules/linear-accumulator examples/modules/linear-accumulator/UniformPrefix.fib
	./build/exec/fibril run --source-dir examples/modules/linear-accumulator examples/modules/linear-accumulator/UniformPrefixFirst.fib
	./build/exec/fibril run --source-dir examples/modules/polymorphic-recursion examples/modules/polymorphic-recursion/Main.fib
	./build/exec/fibril run --source-dir examples/modules/polymorphic-map examples/modules/polymorphic-map/Main.fib
	./build/exec/fibril run --source-dir examples/modules/uniform-recursion examples/modules/uniform-recursion/Main.fib
	./build/exec/fibril run --source-dir examples/modules/uniform-nat-chain examples/modules/uniform-nat-chain/Main.fib
	./build/exec/fibril run --source-dir examples/modules/conditional-recursion examples/modules/conditional-recursion/Main.fib
	./build/exec/fibril run --source-dir examples/modules/mutual-parity examples/modules/mutual-parity/Main.fib
	./build/exec/fibril run --source-dir examples/modules/mutual-parity examples/modules/mutual-parity/Payload.fib
	./build/exec/fibril run --source-dir examples/modules/mutual-parity examples/modules/mutual-parity/Reordered.fib
	./build/exec/fibril run --source-dir examples/modules/motive-contexts examples/modules/motive-contexts/Main.fib
	./build/exec/fibril run --source-dir examples/modules/motive-do examples/modules/motive-do/Main.fib
	./build/exec/fibril run --source-dir examples/modules/direct-data-case examples/modules/direct-data-case/Main.fib
	./build/exec/fibril run --source-dir examples/modules/direct-data-case-dependent examples/modules/direct-data-case-dependent/Main.fib
	./build/exec/fibril run --source-dir test/fixtures/modules/email-service test/fixtures/modules/email-service/Main.fib
	./build/exec/fibril run --source-dir test/fixtures/modules/email-service-full test/fixtures/modules/email-service-full/Main.fib
	./build/exec/fibril run --source-dir examples/modules/pattern-inference examples/modules/pattern-inference/Main.fib
	./build/exec/fibril run --source-dir examples/modules/pattern-inference examples/modules/pattern-inference/Dependent.fib
	./build/exec/fibril run --source-dir examples/modules/pattern-inference examples/modules/pattern-inference/Minimal.fib
	./build/exec/fibril run --source-dir examples/modules/pattern-inference examples/modules/pattern-inference/Named.fib
	./build/exec/fibril run --source-dir examples/modules/pattern-inference examples/modules/pattern-inference/InferredFields.fib
	./build/exec/fibril run --source-dir examples/modules/pattern-inference examples/modules/pattern-inference/InferredParameters.fib

bench:
	python3 tools/benchmark.py
	python3 tools/test_benchmark.py

bench-smoke:
	python3 tools/benchmark.py --quick
	python3 tools/test_benchmark.py

lsp-test: unit-test
	python3 tools/test_lsp.py

# Wait for all compiler build/installation work before invoking editor clients.
editor-test: unit-test
	python3 tools/test_editor.py

python-embed-test:
	python3 tools/test_python_embed.py

docs: unit-test
	IDRIS2_PACKAGE_PATH="$$( $(PACK) --log-level=silence package-path )" \
	IDRIS2_LIBS="$$( $(PACK) --log-level=silence libs-path )" \
	IDRIS2_DATA="$$( $(PACK) --log-level=silence data-path )" \
	$(IDRIS2) --mkdoc fibril.ipkg

handbook: docs
	python3 tools/build_handbook.py
	python3 tools/test_handbook.py

serve-docs: handbook
	python3 tools/serve_handbook.py

clean:
	rm -rf build test/build examples/build bench/build

.PHONY: javascript-runtime javascript-runtime-check javascript-test
javascript-runtime:
	python3 tools/embed_javascript_runtime.py

javascript-runtime-check:
	python3 tools/embed_javascript_runtime.py --check

javascript-test: build
	python3 tools/test_javascript.py

.PHONY: embedded-test
embedded-test: build
	CC="$(CC)" python3 tools/test_embedded.py

.PHONY: network-test network-demo
network-test: build
	CC="$(CC)" python3 tools/test_network.py

network-demo: build
	mkdir -p build/network
	./build/exec/fibril emit-c-network --package examples/modules/tcp-echo/fibril.yaml > build/network/echo.c
	$(CC) $(CFLAGS) -std=c11 -O2 -Wall -Wextra -Werror -I runtime/native build/network/echo.c runtime/native/fibril_network_runtime.c runtime/native/fibril_network.c -o build/network/echo
