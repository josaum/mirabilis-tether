# Makefile — Tether-Optimize v1.1.2 Product Build, Verification & Packaging
SHELL := /bin/bash
VERSION := 1.1.2

.PHONY: all build install uninstall verify verify-lean test doctor pkg web clean

all: build pkg

build:
	@mkdir -p bin dist
	swiftc -O -o bin/tether-events src/tether-events.swift
	@chmod 755 bin/tether-optimize bin/tether-events scripts/*.sh
	@echo "✓ Compiled bin/tether-events"

install:
	./scripts/install.sh

uninstall:
	./scripts/uninstall.sh

verify:
	/Users/josaum/bin/tether-optimize verify

verify-lean:
	/Users/josaum/bin/tether-optimize verify-lean

test:
	/Users/josaum/bin/tether-optimize test

doctor:
	/Users/josaum/bin/tether-optimize doctor

pkg:
	./scripts/build-release.sh

web:
	/usr/bin/open web/index.html

clean:
	rm -rf dist/*.pkg dist/*.tar.gz dist/SHA256SUMS.txt
