import React from "react";
import { renderToStaticMarkup } from "react-dom/server";
import { MarkdownPreview } from "../lib/markdown-preview";

describe("markdown preview", () => {
  it("renders headings and bold text as formatted markup", () => {
    const html = renderToStaticMarkup(
      React.createElement(MarkdownPreview, {
        content: [
          "# Heading",
          "",
          "A paragraph with **bold** text.",
          "",
          "## Details",
        ].join("\n"),
      })
    );

    expect(html).toContain("<h1");
    expect(html).toContain(">Heading</h1>");
    expect(html).toContain("<strong>bold</strong>");
    expect(html).toContain("<h2");
    expect(html).toContain(">Details</h2>");
  });

  it("renders fenced code blocks without altering contents", () => {
    const html = renderToStaticMarkup(
      React.createElement(MarkdownPreview, {
        content: [
          "```ts",
          "const value = 1;",
          "```",
        ].join("\n"),
      })
    );

    expect(html).toContain("<pre");
    expect(html).toContain("<code");
    expect(html).toContain("const value = 1;");
  });
});
