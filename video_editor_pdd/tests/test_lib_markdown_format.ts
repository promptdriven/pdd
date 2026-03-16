import { formatMarkdownDocument } from "../lib/markdown-format";

describe("markdown format", () => {
  it("rewraps prose paragraphs to a stable width", () => {
    const input = `
# Heading

This is a paragraph
that was manually wrapped
across several lines and should be reformatted into stable wrapped output that is visibly different.
`.trim();

    const output = formatMarkdownDocument(input);

    expect(output).toContain("# Heading");
    expect(output).toContain(
      "This is a paragraph that was manually wrapped across several lines and should be"
    );
    expect(output).toContain("reformatted into stable wrapped output that is visibly different.");
    expect(output).not.toContain(
      "This is a paragraph that was manually wrapped across several lines and should be reformatted into stable wrapped output that is visibly different."
    );
  });

  it("preserves list items and block structure while removing extra blank lines", () => {
    const input = `
# Title


- first item that is long enough to be wrapped across multiple lines for a readable markdown list formatter
- second item


## Next

Another paragraph.
`.trim();

    expect(formatMarkdownDocument(input)).toBe([
      "# Title",
      "",
      "- first item that is long enough to be wrapped across multiple lines for a",
      "  readable markdown list formatter",
      "- second item",
      "",
      "## Next",
      "",
      "Another paragraph.",
    ].join("\n"));
  });

  it("preserves fenced code blocks verbatim", () => {
    const input = [
      "# Example",
      "",
      "```ts",
      "const value = 1;",
      "const other = value + 2;",
      "```",
      "",
      "Trailing text",
    ].join("\n");

    expect(formatMarkdownDocument(input)).toBe(input);
  });
});
