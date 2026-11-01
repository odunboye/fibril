PACK ?= pack

.PHONY: build test examples clean
build:
	$(PACK) build fibril

test: build
	$(PACK) test fibril
	./build/exec/fibril --version

examples:
	$(PACK) run fibril-examples

clean:
	rm -rf build test/build examples/build
