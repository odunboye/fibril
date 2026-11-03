PACK ?= pack
IDRIS2 ?= idris2

.PHONY: prelude prelude-check build test editor-test examples bench bench-smoke python-embed-test docs handbook serve-docs clean
prelude:
	python3 tools/embed_prelude.py

prelude-check:
	python3 tools/embed_prelude.py --check

build: prelude-check
	$(PACK) build fibril

test: build
	$(PACK) test fibril
	python3 tools/test_cli.py

examples: build
	$(PACK) run fibril-examples
	./build/exec/fibril manifest examples/manifests/mailer/fibril.yaml
	./build/exec/fibril manifest examples/manifests/email-core/fibril.yaml
	./build/exec/fibril check examples/core/identity.fib
	./build/exec/fibril check examples/core/identity-unicode.fib
	./build/exec/fibril check --erased examples/core/identity-type.fib
	./build/exec/fibril check examples/core/universe-lift.fib
	./build/exec/fibril eval examples/core/evaluate-identity.fib
	./build/exec/fibril check examples/core/identity-annotated.fib
	./build/exec/fibril eval examples/core/local-identity.fib
	./build/exec/fibril eval examples/core/unit.fib
	./build/exec/fibril eval examples/core/consume-unit.fib
	./build/exec/fibril eval examples/core/boolean.fib
	./build/exec/fibril eval examples/core/branch-permissions.fib
	./build/exec/fibril eval examples/core/declarations.fib
	./build/exec/fibril eval examples/core/declarations-polymorphic.fib
	./build/exec/fibril check examples/core/hello-world.fib
	./build/exec/fibril run examples/core/hello-world.fib
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
	./build/exec/fibril run --source-dir examples/modules/visible-implementations examples/modules/visible-implementations/Main.fib
	./build/exec/fibril run --source-dir examples/modules/infix examples/modules/infix/Main.fib
	./build/exec/fibril run --source-dir examples/modules/implementation-factories examples/modules/implementation-factories/Main.fib
	./build/exec/fibril run --source-dir examples/modules/data examples/modules/data/Main.fib
	./build/exec/fibril run --source-dir examples/modules/email-service examples/modules/email-service/Main.fib
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

editor-test:
	python3 tools/test_editor.py

python-embed-test:
	python3 tools/test_python_embed.py

docs: build
	$(IDRIS2) --mkdoc fibril.ipkg

handbook: docs
	python3 tools/build_handbook.py
	python3 tools/test_handbook.py

serve-docs: handbook
	python3 tools/serve_handbook.py

clean:
	rm -rf build test/build examples/build bench/build
