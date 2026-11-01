PACK ?= pack
IDRIS2 ?= idris2

.PHONY: build test examples bench bench-smoke python-embed-test docs handbook serve-docs clean
build:
	$(PACK) build fibril

test: build
	$(PACK) test fibril
	python3 tools/test_cli.py

examples: build
	$(PACK) run fibril-examples
	./build/exec/fibril check examples/core/identity.fib
	./build/exec/fibril check examples/core/identity-unicode.fib
	./build/exec/fibril check --erased examples/core/identity-type.fib
	./build/exec/fibril check examples/core/universe-lift.fib

bench:
	python3 tools/benchmark.py
	python3 tools/test_benchmark.py

bench-smoke:
	python3 tools/benchmark.py --quick
	python3 tools/test_benchmark.py

python-embed-test:
	python3 tools/test_python_embed.py

docs: build
	$(IDRIS2) --mkdoc fibril.ipkg

handbook: docs
	python3 tools/build_handbook.py
	python3 tools/test_handbook.py

serve-docs: handbook
	python3 -m http.server 8000 --bind 127.0.0.1 --directory build/handbook

clean:
	rm -rf build test/build examples/build bench/build
