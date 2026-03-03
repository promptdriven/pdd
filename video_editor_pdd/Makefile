.PHONY: setup dev build test test-remotion test-e2e test-integration test-all

setup:
	./setup.sh

dev:
	npm run dev

build:
	npm run build

test:
	npx jest --no-cache

test-remotion:
	npx jest --no-cache --config=jest.config.remotion.js

test-e2e:
	npx playwright test

test-integration:
	npx playwright test --config=playwright.integration.config.ts

test-all: test test-remotion test-e2e test-integration
