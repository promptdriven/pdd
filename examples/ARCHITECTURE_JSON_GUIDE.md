# Architecture JSON Guide

This guide explains how to use `architecture.json` files in PDD (Prompt-Driven Development) to orchestrate complex code generation workflows.

## What is architecture.json?

The `architecture.json` file is a configuration file that defines a workflow for generating multiple files in a specific order. It allows you to break down complex projects into manageable steps, where each step can depend on the outputs of previous steps.

## Basic Structure

```json
{
  "workflow": [
    {
      "step": 1,
      "description": "Brief description of what this step does",
      "prompt_file": "path/to/prompt.md",
      "output_file": "path/to/output.ext",
      "dependencies": []
    }
  ]
}
```

## Key Components

### workflow
An array of step objects that define the generation sequence.

### step
A unique identifier for the step (typically a number).

### description
A human-readable description of what the step accomplishes.

### prompt_file
Path to the prompt file (relative to the project root) that contains the instructions for this step.

### output_file
Path where the generated content should be saved.

### dependencies
An array of step numbers that must complete before this step can run.

## Example: Simple Website Generation

```json
{
  "workflow": [
    {
      "step": 1,
      "description": "Generate HTML structure",
      "prompt_file": "prompts/html_structure.md",
      "output_file": "index.html",
      "dependencies": []
    },
    {
      "step": 2,
      "description": "Generate CSS styles",
      "prompt_file": "prompts/css_styles.md",
      "output_file": "styles.css",
      "dependencies": [1]
    },
    {
      "step": 3,
      "description": "Add JavaScript interactivity",
      "prompt_file": "prompts/javascript.md",
      "output_file": "script.js",
      "dependencies": [1, 2]
    }
  ]
}
```

## Running the Workflow

To execute an architecture.json workflow, use:

```bash
pdd sync <step_number>
```

For example:
- `pdd sync 1` - Run only step 1
- `pdd sync 3` - Run steps 1, 2, and 3 (respecting dependencies)

## Best Practices

### 1. Logical Step Ordering
Order your steps logically, with foundational components first:
- Step 1: Core structure (HTML, main classes)
- Step 2: Styling (CSS)
- Step 3: Interactivity (JavaScript)
- Step 4: Integration and refinement

### 2. Clear Dependencies
Use dependencies to ensure steps run in the correct order:
```json
{
  "step": 3,
  "dependencies": [1, 2]  // This step needs steps 1 and 2 to complete first
}
```

### 3. Descriptive Names
Use clear, descriptive names for prompt files and output files:
- `prompts/html_structure.md` instead of `prompts/step1.md`
- `components/header.html` instead of `output1.html`

### 4. Modular Prompts
Keep each prompt focused on a single responsibility:
- One prompt for HTML structure
- One prompt for CSS styling
- One prompt for JavaScript functionality

## Advanced Features

### Conditional Steps
You can create steps that only run under certain conditions by using dependencies strategically.

### Multi-file Generation
A single step can generate multiple related files by using comprehensive prompts.

### Iterative Refinement
Later steps can refine or modify files created in earlier steps.

## Example Projects

Check out these example projects that use architecture.json:

- `hello/` - Simple Python application
- `handpaint/` - Web-based drawing application
- `pi_calc/` - Mathematical calculation tool

## Troubleshooting

### Common Issues

1. **Step not running**: Check that all dependencies are satisfied
2. **File not found**: Verify prompt_file paths are correct relative to project root
3. **Output conflicts**: Ensure output_file paths don't conflict between steps

### Debugging Tips

- Run steps individually to isolate issues
- Check that prompt files exist and are readable
- Verify output directories exist or can be created

## That's it!

You now have the knowledge to create powerful, orchestrated code generation workflows using architecture.json files. Start simple and gradually build more complex workflows as you become comfortable with the system.