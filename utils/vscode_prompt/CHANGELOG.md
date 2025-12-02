# Change Log

All notable changes to the "prompt-highlighter" extension are documented here.

This project follows the guidelines from [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and aims to use [Semantic Versioning](https://semver.org/).


## [0.0.3] - 2025-10-24

### Added
- **PDD CLI Installation System**
  - Intelligent detection across multiple installation methods (uv tools and common paths)
  - Automatic uv installation with user consent and clear explanations
  - Cross-platform support for macOS, Linux, and Windows
  - Command Palette integration with four commands:
    - `PDD: Install PDD CLI` - Install the PDD command-line tool
    - `PDD: Check PDD CLI Installation` - Verify installation status
    - `PDD: Run PDD Setup` - Configure API keys and tab completion
    - `PDD: Upgrade to uv Installation` - Ensure using latest uv-based installation
  - Setup is optional
  - Toast notifications instead of modal dialogs for better UX
  - Comprehensive test suite with 31 passing tests

### Changed
- Simplified installation architecture by removing conda environment support
- Removed pip installation method - uv is now the only installation method
- PDD CLI now installs exclusively via uv (the modern Python package manager)
- Updated detection logic to check base anaconda/miniconda paths instead of dedicated conda environments 

Thank you Danial Toktarbayev for your contributions!

## [0.0.2] - 2025-09-23

### Changed
- Broaden compatibility messaging to cover OpenVSX‑compatible IDEs (VS Code, Cursor, VSCodium, Gitpod, Kiro, Windsurf, etc.).
- Update `package.json` description and keywords for discoverability in OpenVSX ecosystems.
- Refresh README and quickstart with installation instructions for VSCodium, Kiro, Windsurf, and other OpenVSX‑compatible editors.
- Improve Makefile `install` target messaging to mention additional editor CLIs.

### Notes
- No changes to the TextMate grammar or language configuration; this is a documentation/metadata update to reflect wider IDE support.

## [0.0.1] - 2025-09-09

### Added
- Initial release of Prompt Driven Development syntax support.
- TextMate grammar for `.prompt` files (syntax highlighting).
- Language configuration (comments, brackets, editor behaviors).
- Extension icon and basic branding.
- README and quickstart documentation.
