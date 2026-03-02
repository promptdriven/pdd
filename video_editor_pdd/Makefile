.PHONY: setup dev build test test-e2e test-integration test-all

setup:
	./setup.sh

dev:
	npm run dev

build:
	npm run build

test:
	npx jest --no-cache

test-e2e:
	npx playwright test

test-integration:
	npx playwright test --config=playwright.integration.config.ts

test-all: test test-e2e test-integration
