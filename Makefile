PACK ?= pack
IDRIS2 ?= idris2

.PHONY: build test examples docs clean
build:
	$(PACK) build fibril

test: build
	$(PACK) test fibril
	./build/exec/fibril --version

examples:
	$(PACK) run fibril-examples

docs: build
	$(IDRIS2) --mkdoc fibril.ipkg

clean:
	rm -rf build test/build examples/build
