import {
  extractNarrationSyncQuotes,
  findMatchingScriptSection,
  normalizeSectionKey,
  parseScriptSections,
  scriptLineMatchesNarration,
} from "@/lib/spec-script-context";

describe("spec script context helpers", () => {
  const sampleScript = [
    "# Test Script",
    "",
    "## PART 1: Economics",
    "",
    "**[VISUAL: [Remotion] A graph rises from left to right.]**",
    "",
    "**NARRATOR:**",
    "Markets moved quickly.",
    "",
    "## Animation Section",
    "",
    "**NARRATOR:**",
    "Animated circles tell the story.",
  ].join("\n");

  it("normalizes labels, ids, and headings into the same comparable key", () => {
    expect(normalizeSectionKey("Part 1: Economics")).toBe("part 1 economics");
    expect(normalizeSectionKey("part1_economics")).toBe("part 1 economics");
    expect(normalizeSectionKey("ANIMATION SECTION")).toBe("animation section");
  });

  it("parses script headings into section-scoped line groups with line numbers", () => {
    const sections = parseScriptSections(sampleScript);

    expect(sections).toHaveLength(2);
    expect(sections[0].heading).toBe("PART 1: Economics");
    expect(sections[0].startLine).toBe(3);
    expect(sections[0].lines).toEqual([
      expect.objectContaining({
        kind: "visual",
        lineNumber: 5,
        text: "[Remotion] A graph rises from left to right.",
      }),
      expect.objectContaining({
        kind: "narrator",
        lineNumber: 7,
        text: "NARRATOR",
      }),
      expect.objectContaining({
        kind: "text",
        lineNumber: 8,
        text: "Markets moved quickly.",
      }),
    ]);
  });

  it("matches a project section against the best script section using label or id", () => {
    const sections = parseScriptSections(sampleScript);

    expect(
      findMatchingScriptSection(sections, {
        id: "part1_economics",
        label: "Part 1: Economics",
      })?.heading
    ).toBe("PART 1: Economics");

    expect(
      findMatchingScriptSection(sections, {
        id: "animation_section",
        label: "Animation Section",
      })?.heading
    ).toBe("Animation Section");
  });

  it("extracts Narration Sync quotes from a generated spec", () => {
    const specContent = [
      "# Section 1.1: Economics Graph",
      "",
      "## Narration Sync",
      '> "Markets moved quickly."',
      '> "Animated circles tell the story."',
      "",
      "## Code Structure (Remotion)",
      "```typescript",
      "<Sequence />",
      "```",
    ].join("\n");

    expect(extractNarrationSyncQuotes(specContent)).toEqual([
      "Markets moved quickly.",
      "Animated circles tell the story.",
    ]);
  });

  it("highlights only script text lines that match Narration Sync quotes", () => {
    const section = parseScriptSections(sampleScript)[0];
    const narrationQuotes = ["Markets moved quickly."];

    expect(scriptLineMatchesNarration(section.lines[0], narrationQuotes)).toBe(false);
    expect(scriptLineMatchesNarration(section.lines[1], narrationQuotes)).toBe(false);
    expect(scriptLineMatchesNarration(section.lines[2], narrationQuotes)).toBe(true);
  });
});
