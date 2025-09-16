# Examples

This directory contains examples that demonstrate comparisons between using Cursor and Prompt-Driven Development (PDD) for various programming tasks. These examples serve as practical illustrations of how PDD can be used to generate and modify code, via the pdd sync command, and how it compares to traditional development approaches.

## Getting Started

### Post-Installation Setup (Required first step after installation)

Before running any examples, make sure you've completed the PDD setup:

```bash
pdd setup
```

This command will guide you through:
- Installing shell tab completion
- Capturing your API keys
- Creating ~/.pdd configuration files
- Writing the starter prompt

After setup, reload your shell:
```bash
source ~/.zshrc  # or source ~/.bashrc / fish equivalent
```

## Available Examples

### Handpaint
The handpaint example demonstrates how PDD can be used to create and modify a painting application. This example shows:
- How PDD can be used to generate code for a graphical application
- The process of iteratively refining code through PDD
- A comparison between traditional development and PDD-assisted development

### Hello World
The hello_world example demonstrates how PDD can be used to generate code for a simple Python function that prints "hello". This example shows:
- How PDD can be used to generate code for a simple Python function via the sync command

### Pi Calc
The pi_calc example demonstrates how PDD can be used to generate code for a simple Python function that calculates the value of Pi. This example shows:
- How PDD can be used to generate code for a simple Python function using the sync command

### QR Code Sandwich
The qrcode_sandwich example demonstrates how PDD can be used to generate code that produces scannable QR codes embedded within photorealistic images using ControlNet QR conditioning. This example shows:
- Creating a QR code that blends into a realistic image while remaining scannable
- Leveraging ControlNet QR conditioning in a generated Python script
- Iterating with PDD to refine parameters and results

More examples will be added to this directory as they are developed.

## Purpose
These examples are designed to help developers understand:
1. The capabilities of PDD in different programming contexts
2. How PDD compares to traditional development workflows
3. Best practices for using PDD effectively
4. Real-world applications of PDD in various domains

Each example includes documentation and code that can be used as a reference for your own PDD-based development projects.
