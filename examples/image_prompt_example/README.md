# Image Prompt Example (Advanced)

This example demonstrates how to use an image as a visual specification for code generation. The model is instructed to **understand** the content of the image and generate code that replicates its appearance, rather than simply displaying the image file.

## How to Include Images in a Prompt

To include an image in a prompt, use the `<image>` tag with the path to the image file. You can include multiple images in a single prompt.

```xml
<image>path/to/your/image.png</image>
```

The supported image formats are:

*   `.png`
*   `.jpg`
*   `.jpeg`
*   `.gif`
*   `.webp`

## How to Run This Example

To run this example, use the `pdd generate` command. The image is included directly in the prompt file using the `<image>` tag.

```bash
pdd generate examples/image_prompt_example/describe_python.prompt --output examples/image_prompt_example/describe.py
```

This command will generate a Python file named `describe.py`. When you run this script, it will print a detailed description of the image, proving the model understood the visual content.