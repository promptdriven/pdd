SHELL := /bin/bash

NAME := $(shell node -p "require('./package.json').name")
VERSION := $(shell node -p "require('./package.json').version")
PUBLISHER := $(shell node -p "require('./package.json').publisher")
EXT_ID := $(PUBLISHER).$(NAME)
VSIX := $(NAME)-$(VERSION).vsix

.PHONY: help icon thumb package publish clean verify install uninstall reinstall vsix

help:
	@echo "Targets:"
	@echo "  icon      - Render images/icon.png from images/icon.svg"
	@echo "  thumb     - Build images/video-thumb.png from YouTube cover"
	@echo "  package   - Create $(VSIX) using vsce (or npx @vscode/vsce)"
	@echo "  publish   - Publish to Marketplace (requires VSCODE_PAT)"
	@echo "  install   - Local install of $(VSIX) into VS Code (or Insiders/Codium/Cursor)"
	@echo "  uninstall - Remove installed extension ($(EXT_ID)) from local editor(s)"
	@echo "  reinstall - Uninstall then install the built VSIX"
	@echo "  verify    - Quick sanity check of package.json"
	@echo "  clean     - Remove generated images and .vsix files"

icon: images/icon.png

images/icon.png: images/icon.svg scripts/render-icon.mjs package.json
	node scripts/render-icon.mjs

thumb: images/video-thumb.png

images/video-thumb.png: scripts/generate-video-thumb.mjs package.json
	npm run build-video-thumb

vsix: package

package: icon
	@if command -v vsce >/dev/null 2>&1; then \
	  echo "Using system vsce"; \
	  vsce package; \
	else \
	  echo "vsce not found; using npx @vscode/vsce"; \
	  npx @vscode/vsce package; \
	fi

install: package
	@set -e; \
	for cli in code code-insiders codium cursor; do \
	  if command -v $$cli >/dev/null 2>&1; then \
	    echo "Installing $(VSIX) with $$cli"; \
	    $$cli --install-extension $(VSIX) --force; \
	    echo "Installed into $$cli"; \
	    exit 0; \
	  fi; \
	done; \
	echo "No supported editor CLI found (code/code-insiders/codium/cursor)."; \
	exit 1

uninstall:
	@set -e; \
	FOUND=0; \
	for cli in code code-insiders codium cursor; do \
	  if command -v $$cli >/dev/null 2>&1; then \
	    FOUND=1; \
	    echo "Uninstalling $(EXT_ID) from $$cli (ignore if not installed)"; \
	    $$cli --uninstall-extension $(EXT_ID) || true; \
	  fi; \
	done; \
	if [ "$$FOUND" -eq 0 ]; then \
	  echo "No supported editor CLI found (code/code-insiders/codium/cursor)."; \
	  exit 1; \
	fi; \
	echo "Uninstall attempted across available editors."

reinstall: uninstall install

publish: icon
	@if [ -z "$$VSCODE_PAT" ]; then \
	  echo "Error: VSCODE_PAT env var is required to publish"; \
	  echo "Create a Personal Access Token and export VSCODE_PAT, then re-run."; \
	  exit 1; \
	fi
	@if command -v vsce >/dev/null 2>&1; then \
	  echo "Using system vsce"; \
	  vsce publish; \
	else \
	  echo "vsce not found; using npx @vscode/vsce"; \
	  npx @vscode/vsce publish; \
	fi

verify:
	node -e "JSON.parse(require('fs').readFileSync('package.json')); console.log('package.json OK')"

clean:
	rm -f images/icon.png images/video-thumb.png *.vsix
