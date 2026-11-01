PACK ?= pack

.PHONY: build test clean
build:
	$(PACK) build fibril

test: build
	$(PACK) test fibril
	./build/exec/fibril --version

clean:
	rm -rf build test/build
