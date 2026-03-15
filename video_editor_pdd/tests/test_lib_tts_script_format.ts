import { buildCanonicalTtsScript } from "../lib/tts-script-format";

describe("lib/tts-script-format", () => {
  it("rewrites headingless generated narration into canonical section-based format", () => {
    const mainScript = [
      "## Intro",
      "",
      "**NARRATOR:**",
      "Hello from the intro.",
      "",
      "## Outro",
      "",
      "**NARRATOR:**",
      "Goodbye from the outro.",
      "",
    ].join("\n");

    const rawTtsScript = [
      "# TTS Script",
      "",
      "[TONE: warm]",
      "[PACE: moderate]",
      "Hello from the intro.",
      "",
      "[PAUSE: 1.2s]",
      "[TONE: calm]",
      "Goodbye from the outro.",
      "",
    ].join("\n");

    const output = buildCanonicalTtsScript(
      mainScript,
      rawTtsScript,
      [
        { id: "intro", label: "Intro" },
        { id: "outro", label: "Outro" },
      ],
    );

    expect(output).toContain("## Intro");
    expect(output).toContain("## Outro");
    expect(output).toContain("[TONE: warm]");
    expect(output).toContain("[TONE: calm]");
    expect(output).toContain("Hello from the intro.");
    expect(output).toContain("Goodbye from the outro.");
    expect(output).toContain("[PAUSE: 1.2s]");
  });

  it("falls back to default tags when Claude omits annotation markers", () => {
    const mainScript = [
      "## Main Section",
      "",
      "**NARRATOR:**",
      "This is the only line.",
      "",
    ].join("\n");

    const output = buildCanonicalTtsScript(
      mainScript,
      "This is the only line.\n",
      [{ id: "main_section", label: "Main Section" }],
    );

    expect(output).toContain("## Main Section");
    expect(output).toContain("[TONE: explanatory]");
    expect(output).toContain("[PACE: moderate]");
    expect(output).toContain("[EMOTION: calm]");
    expect(output).toContain("This is the only line.");
  });
});
