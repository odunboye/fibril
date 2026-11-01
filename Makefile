IDRIS2 ?= idris2

.PHONY: build test clean
build:
	$(IDRIS2) --build fibril.ipkg

test: build
	$(IDRIS2) --build tests.ipkg
	./build/exec/fibril-tests
	./build/exec/fibril --version

clean:
	rm -rf build
