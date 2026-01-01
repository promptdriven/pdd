# PDD (Prompt-Driven Development) Command Line Interface

![PDD-CLI Version](https://img.shields.io/badge/pdd--cli-v0.0.98-blue) [![Discord](https://img.shields.io/badge/Discord-join%20chat-7289DA.svg?logo=discord&logoColor=white)](https://discord.gg/Yp4RTh8bG7)

## Introduction

Pdd-cli is a complete AI toolchain for generating and maintaining codebases **reliably and repeatably** using the prompt-driven approach.

Unique to this approach, **each PDD prompt is a mini-spec of a single output file**.  PDD fully generates one entire code file at a time, giving you tight control and ensuring each output file is reliably re-generated from its prompt.   

By contrast, prompts in typical AI coding tools are instead incremental patch requests, and these tools will unpredictably update any combination of files in response to a  prompt.   PDD is an excellent complement to such tools - for long-lived codebases and tasks that are repeatedly rebuilt as they evolve, use PDD; for more incremental, one-off, or ephemeral tasks, use agentic coders, such as Claude, Codex, etc.

<p align="center">
  <img src="docs/videos/handpaint_demo.gif" alt="PDD Handpaint Demo" />
</p>

Noteworthy among its many features, PDD accumulates unit and regression tests, as it detects and fixes bugs, and updates your prompts automatically whenever needed.    In short, it endeavors to fully upport the entire prompt-driven approach.
<br>


## Prerequisites before installing pdd-cli

* MacOS: xcode cli tools, and either uv or pip  [see instructions](README-INSTALL-PREREQS.md)
* Linux: uv or pip [see instructions](README-INSTALL-PREREQS.md)
* Windows: [click here](SETUP_WITH_WINDOWS.md) for complete Windows installation instructions

## Quick Installation

### uv (recommended)
```bash
uv tool install pdd-cli
```

### pip (alternate method)
```bash
pip install pdd-cli
```


### Then run pdd to check:
```bash
pdd --version
```
<br> 

From here your pdd installation is complete.   For the most convenience, set up your LLM API keys, as below:<br><br><br>

## Configure your API keys & shell

```bash
# Creates api-env and llm_model.csv config files in ~/.pdd, add tab completions, and updates shell init.
# It also writes a starter prompt (success_python.prompt) for you to try.   

# Re-run this any time to update keys or reinstall completions.   

pdd setup
```
```bash
# Reload your shell so the new completion and environment hooks are available:

. ~/.zshrc  # or ". ~/.bashrc" / or fish equivalent
```


(If you skip this step, PDD commands will print a reminder banner so you can finish onboarding later.)

Optional: at this poing you can [begin customizing PDD behavior](README-ADVANCED-CONFIGURATION.md#minimum-configuration)

<br><br>
## Then try it out:
```bash
pdd generate success_python.prompt
```
(**Extra credit!!!** -- Build the various examples included in pdd repo, under **pdd/examples/**.  <br>
  Just do `git clone https://github.com/promptdriven/pdd.git`)
<br><br>

## Next steps:

* Review [PDD Fundamental Concepts and Practices](README-CONCEPTS.md) to get oriented to the PDD approach.

* Start incorporating individual [Prompt-Driven Workflows](README-WORKFLOWS.md) into your development cycle.

* [Join the PDD Discord Community](http://tinyurl.com/pdd-discord), and [Contribute to PDD](CONTRIBUTING.md).

## Going deeper
* [PDD Command Reference](README-COMMANDS.md) 
* [Troubleshooting](README-TROUBLESHOOTING.md)
* [Advanced Configuration for Your Project](README-ADVANCED-CONFIGURATION.md)
* [PDD Cloud](README-CLOUD.md)
* [Security Considerations](README-SECURITY.md)
* [Gemini API key instructions](SETUP_WITH_GEMINI.md)

## Whitepaper

For a detailed explanation of the concepts, architecture, and benefits of Prompt-Driven Development, please refer to our full whitepaper. This document provides an in-depth look at the PDD philosophy, its advantages over traditional development, and includes benchmarks and case studies.

[Read the Full Whitepaper with Benchmarks](docs/whitepaper_with_benchmarks/whitepaper_w_benchmarks.md)

Also see the Prompt‑Driven Development Doctrine for core principles and practices: [docs/prompt-driven-development-doctrine.md](docs/prompt-driven-development-doctrine.md)


## Patents

One or more patent applications covering aspects of the PDD workflows and systems are pending. This notice does not grant any patent rights; rights are as specified in the [LICENSE](LICENSE).
