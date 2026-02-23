/**
 * Tests for app/layout.tsx
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/app_layout_typescriptreact.prompt.
 *
 * Spec requirements verified:
 *   1. Exports `metadata: Metadata` with `title: 'Video Pipeline Editor'`
 *      and `description: 'AI-powered video production pipeline'`.
 *   2. `<html lang="en" className="dark">` with `dark` class for Tailwind dark mode.
 *   3. `<body>` with `className="bg-panel text-slate-200 antialiased"`.
 *   4. Imports `./globals.css` at the top.
 *   5. Wraps children in a `<main>` element with `className="h-screen overflow-hidden"`.
 *   6. No client-side state — this is a server component (no `'use client'`).
 *   7. Exports `RootLayout` as default.
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Source code (loaded once for structural tests)
// ---------------------------------------------------------------------------

const SOURCE_PATH = path.join(__dirname, "..", "app", "layout.tsx");
const sourceCode = fs.readFileSync(SOURCE_PATH, "utf-8");

// ---------------------------------------------------------------------------
// 1. Module structure
// ---------------------------------------------------------------------------

describe("module structure", () => {
  it("file exists at expected path", () => {
    expect(fs.existsSync(SOURCE_PATH)).toBe(true);
  });

  it("is a TypeScript React file", () => {
    expect(SOURCE_PATH).toMatch(/\.tsx$/);
  });

  it("exports RootLayout as default function", () => {
    expect(sourceCode).toMatch(/export\s+default\s+function\s+RootLayout/);
  });

  it("RootLayout accepts { children } prop typed as React.ReactNode", () => {
    expect(sourceCode).toMatch(/children\s*:\s*React\.ReactNode/);
  });
});

// ---------------------------------------------------------------------------
// 2. Server component — no 'use client' directive (Req 6)
// ---------------------------------------------------------------------------

describe("server component", () => {
  it("does NOT contain 'use client' directive", () => {
    expect(sourceCode).not.toMatch(/['"]use client['"]/);
  });

  it("does not use useState", () => {
    expect(sourceCode).not.toContain("useState");
  });

  it("does not use useEffect", () => {
    expect(sourceCode).not.toContain("useEffect");
  });

  it("does not use useRef", () => {
    expect(sourceCode).not.toContain("useRef");
  });
});

// ---------------------------------------------------------------------------
// 3. Metadata export (Req 1)
// ---------------------------------------------------------------------------

describe("metadata export", () => {
  it("exports a const named metadata", () => {
    expect(sourceCode).toMatch(/export\s+const\s+metadata/);
  });

  it("metadata is typed as Metadata from next", () => {
    expect(sourceCode).toMatch(/metadata:\s*Metadata/);
  });

  it("imports Metadata type from 'next'", () => {
    expect(sourceCode).toMatch(/import\s+type\s*\{\s*Metadata\s*\}\s*from\s*['"]next['"]/);
  });

  it("title is 'Video Pipeline Editor'", () => {
    expect(sourceCode).toMatch(/title:\s*['"]Video Pipeline Editor['"]/);
  });

  it("description is 'AI-powered video production pipeline'", () => {
    expect(sourceCode).toMatch(/description:\s*['"]AI-powered video production pipeline['"]/);
  });
});

// ---------------------------------------------------------------------------
// 4. HTML element with dark class (Req 2)
// ---------------------------------------------------------------------------

describe("html element", () => {
  it("renders <html> with lang='en'", () => {
    expect(sourceCode).toMatch(/<html\s[^>]*lang=["']en["']/);
  });

  it("renders <html> with className='dark'", () => {
    expect(sourceCode).toMatch(/<html\s[^>]*className=["']dark["']/);
  });
});

// ---------------------------------------------------------------------------
// 5. Body element with correct classes (Req 3)
// ---------------------------------------------------------------------------

describe("body element", () => {
  it("renders <body> element", () => {
    expect(sourceCode).toMatch(/<body/);
  });

  it("body has bg-panel class", () => {
    expect(sourceCode).toMatch(/<body\s[^>]*className=["'][^"']*bg-panel/);
  });

  it("body has text-slate-200 class", () => {
    expect(sourceCode).toMatch(/<body\s[^>]*className=["'][^"']*text-slate-200/);
  });

  it("body has antialiased class", () => {
    expect(sourceCode).toMatch(/<body\s[^>]*className=["'][^"']*antialiased/);
  });

  it("body className contains exactly 'bg-panel text-slate-200 antialiased'", () => {
    expect(sourceCode).toMatch(/<body\s+className=["']bg-panel text-slate-200 antialiased["']/);
  });
});

// ---------------------------------------------------------------------------
// 6. Globals CSS import (Req 4)
// ---------------------------------------------------------------------------

describe("globals.css import", () => {
  it("imports './globals.css'", () => {
    expect(sourceCode).toMatch(/import\s+['"]\.\/globals\.css['"]/);
  });

  it("globals.css import is near the top of the file (within first 5 lines)", () => {
    const lines = sourceCode.split("\n");
    const importLineIndex = lines.findIndex((line: string) =>
      /import\s+['"]\.\/globals\.css['"]/.test(line)
    );
    expect(importLineIndex).toBeGreaterThanOrEqual(0);
    expect(importLineIndex).toBeLessThan(5);
  });
});

// ---------------------------------------------------------------------------
// 7. Main wrapper element (Req 5)
// ---------------------------------------------------------------------------

describe("main wrapper element", () => {
  it("renders <main> element wrapping children", () => {
    expect(sourceCode).toMatch(/<main/);
  });

  it("main has h-screen class", () => {
    expect(sourceCode).toMatch(/<main\s[^>]*className=["'][^"']*h-screen/);
  });

  it("main has overflow-hidden class", () => {
    expect(sourceCode).toMatch(/<main\s[^>]*className=["'][^"']*overflow-hidden/);
  });

  it("main className contains exactly 'h-screen overflow-hidden'", () => {
    expect(sourceCode).toMatch(/<main\s+className=["']h-screen overflow-hidden["']/);
  });

  it("main wraps {children}", () => {
    expect(sourceCode).toMatch(/<main[^>]*>\s*\{children\}\s*<\/main>/);
  });
});

// ---------------------------------------------------------------------------
// 8. DOM hierarchy
// ---------------------------------------------------------------------------

describe("DOM hierarchy", () => {
  it("html contains body", () => {
    const htmlStart = sourceCode.indexOf("<html");
    const bodyStart = sourceCode.indexOf("<body");
    const htmlEnd = sourceCode.indexOf("</html>");
    expect(bodyStart).toBeGreaterThan(htmlStart);
    expect(bodyStart).toBeLessThan(htmlEnd);
  });

  it("body contains main", () => {
    const bodyStart = sourceCode.indexOf("<body");
    const mainStart = sourceCode.indexOf("<main");
    const bodyEnd = sourceCode.indexOf("</body>");
    expect(mainStart).toBeGreaterThan(bodyStart);
    expect(mainStart).toBeLessThan(bodyEnd);
  });

  it("main contains {children}", () => {
    const mainStart = sourceCode.indexOf("<main");
    const childrenPos = sourceCode.indexOf("{children}");
    const mainEnd = sourceCode.indexOf("</main>");
    expect(childrenPos).toBeGreaterThan(mainStart);
    expect(childrenPos).toBeLessThan(mainEnd);
  });
});

// ---------------------------------------------------------------------------
// 9. Minimalism — no extra providers or client features
// ---------------------------------------------------------------------------

describe("minimalism", () => {
  it("does not import React Query", () => {
    expect(sourceCode).not.toMatch(/react-query|@tanstack\/react-query/);
  });

  it("does not import any context providers", () => {
    expect(sourceCode).not.toMatch(/Provider/);
  });

  it("does not use next/font", () => {
    expect(sourceCode).not.toMatch(/next\/font/);
  });

  it("file is concise (under 30 lines)", () => {
    const lineCount = sourceCode.split("\n").length;
    expect(lineCount).toBeLessThan(30);
  });
});
