PACK ?= pack
IDRIS2 ?= idris2

.PHONY: build test examples docs handbook serve-docs clean
build:
	$(PACK) build fibril

test: build
	$(PACK) test fibril
	./build/exec/fibril --version

examples:
	$(PACK) run fibril-examples

docs: build
	$(IDRIS2) --mkdoc fibril.ipkg

handbook: docs
	python3 tools/build_handbook.py
	python3 tools/test_handbook.py

serve-docs: handbook
	python3 -m http.server 8000 --bind 127.0.0.1 --directory build/handbook

clean:
	rm -rf build test/build examples/build
