# Contributing to PDD CLI

First off, thank you for considering contributing to PDD CLI! It's people like you that make open source projects thrive.

This document provides guidelines for contributing to the project. Please feel free to propose changes to this document in a pull request.

## How Can I Contribute?

* **Reporting Bugs:** If you find a bug, please open an issue detailing the problem, how to reproduce it, and your environment.
* **Suggesting Enhancements:** Open an issue to suggest new features or improvements to existing functionality.
* **Pull Requests:** If you've fixed a bug or implemented a new feature, feel free to submit a pull request.

## Development Setup

1. **Clone the repository:**
   ```bash
   git clone https://github.com/promptdriven/pdd.git
   cd pdd
   ```
2. **Create and activate a Conda environment:** (Recommended)
   We recommend using Conda to manage dependencies in an isolated environment. Make sure you have Miniconda or Anaconda installed.
   ```bash
   # Create an environment named 'pdd' (or choose your own name)
   conda create -n pdd python=3.12
   conda activate pdd
   ```
3. **Install dependencies:**
   Install the package in editable mode along with all development dependencies:
   ```bash
   pip install -e .[dev]
   ```

   This command installs the runtime dependencies specified in `pyproject.toml` as well as the development tools listed under `[project.optional-dependencies].dev`.

## Running Tests

To ensure code quality and prevent regressions, please run the test suite:

```bash
pytest
```

You can also run tests with coverage reporting:

```bash
pytest --cov=pdd
```

## Building the Package

If you need to build the distributable package files (wheel and source distribution):

1. **Install the build tool:** (If not already installed)
   ```bash
   pip install build
   ```
2. **Run the build process:**
   Execute this command from the project root directory:
   ```bash
   python -m build
   ```

   This will create a `dist/` directory containing the `.whl` (wheel) and `.tar.gz` (source distribution) files.

## Publishing a Release (Maintainers)

This section is primarily for project maintainers.

1. **Ensure the build artifacts are up-to-date:**
   Run the build process as described above.
2. **Install Twine:** (If not already installed)
   Twine is used to securely upload packages to PyPI.
   ```bash
   pip install twine
   ```
3. **Upload to PyPI:**
   Use Twine to upload the artifacts from the `dist/` directory. You will need appropriate credentials for the PyPI project.
   ```bash
   twine upload dist/*
   ```

   Follow the prompts to enter your PyPI username and password (or use an API token).

## Pull Request Process

1. Ensure any install or build dependencies are removed before committing.
2. Update the `README.md` with details of changes to the interface, this includes new environment variables, exposed ports, useful file locations, and container parameters.
3. Increase the version numbers in `pyproject.toml` and the `README.md` to the new version that this Pull Request would represent. The versioning scheme we use is [SemVer](http://semver.org/).
4. You may merge the Pull Request in once you have the sign-off of two other developers, or if you do not have permission to do that, you may request the second reviewer to merge it for you.

Thank you for your contributions!
