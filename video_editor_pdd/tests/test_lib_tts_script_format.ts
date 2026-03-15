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
    expect(output).toContain("[INSTRUCT:");
    expect(output).toContain("Hello from the intro.");
    expect(output).toContain("Goodbye from the outro.");
    expect(output).toContain("[PAUSE: 1.2s]");
  });

  it("preserves explicit [INSTRUCT:] lines from generated output", () => {
    const mainScript = [
      "## Intro",
      "",
      "**NARRATOR:**",
      "Hello from the intro.",
      "",
    ].join("\n");

    const rawTtsScript = [
      "[TONE: warm]",
      "[PACE: moderate]",
      "[INSTRUCT: Speak warmly and reassuringly.]",
      "Hello from the intro.",
      "",
    ].join("\n");

    const output = buildCanonicalTtsScript(
      mainScript,
      rawTtsScript,
      [{ id: "intro", label: "Intro" }],
    );

    expect(output).toContain("[INSTRUCT: Speak warmly and reassuringly.]");
  });

  it("maps generated blocks into the correct sections when source headings include subtitles and time ranges", () => {
    const mainScript = [
      "## COLD OPEN: THE SOCK HOOK (0:00 - 2:00)",
      "",
      "**NARRATOR:**",
      "Cold open line one.",
      "",
      "**[VISUAL: Hold on the split screen.]**",
      "",
      "Cold open line two.",
      "",
      "## PART 1: THE ECONOMICS OF DARNING (2:30 - 8:30)",
      "",
      "**NARRATOR:**",
      "Part one line one.",
      "",
      "**[VISUAL: Chart annotation appears.]**",
      "",
      "Part one line two.",
      "",
      "## CLOSING (24:15 - 25:00)",
      "",
      "**NARRATOR:**",
      "Closing line one.",
      "",
    ].join("\n");

    const rawTtsScript = [
      "[TONE: bright]",
      "Cold open line one.",
      "[PAUSE: 0.8s]",
      "",
      "[TONE: bright]",
      "Cold open line two.",
      "[PAUSE: 0.8s]",
      "",
      "[TONE: explanatory]",
      "Part one line one.",
      "[PAUSE: 1.0s]",
      "",
      "[TONE: explanatory]",
      "Part one line two.",
      "[PAUSE: 1.0s]",
      "",
      "[TONE: final]",
      "Closing line one.",
      "",
    ].join("\n");

    const output = buildCanonicalTtsScript(
      mainScript,
      rawTtsScript,
      [
        { id: "cold_open", label: "Cold Open" },
        { id: "part1_economics", label: "Part 1: The Economics of Darning" },
        { id: "closing", label: "Closing" },
      ],
    );

    expect(output).toContain(
      [
        "## Cold Open",
        "",
        "[TONE: bright]",
        "[INSTRUCT: Speak with a confident, authoritative tone like a knowledgeable educator, with a bright tone.]",
        "Cold open line one.",
        "[PAUSE: 0.8s]",
        "",
        "[TONE: bright]",
        "[INSTRUCT: Speak with a confident, authoritative tone like a knowledgeable educator, with a bright tone.]",
        "Cold open line two.",
      ].join("\n"),
    );
    expect(output).toContain(
      [
        "## Part 1: The Economics of Darning",
        "",
        "[TONE: explanatory]",
        "[INSTRUCT: Speak with a confident, authoritative tone like a knowledgeable educator, with a explanatory tone.]",
        "Part one line one.",
        "[PAUSE: 1.0s]",
        "",
        "[TONE: explanatory]",
        "[INSTRUCT: Speak with a confident, authoritative tone like a knowledgeable educator, with a explanatory tone.]",
        "Part one line two.",
      ].join("\n"),
    );
    expect(output).toContain(
      [
        "## Closing",
        "",
        "[TONE: final]",
        "[INSTRUCT: Speak with a confident, authoritative tone like a knowledgeable educator, with a final tone.]",
        "Closing line one.",
      ].join("\n"),
    );
    expect(output).not.toContain("## Part 1: The Economics of Darning\n\n---");
  });

  it("extracts multiple spoken paragraphs from a single narrator section across visual markers", () => {
    const mainScript = [
      "## Main Section",
      "",
      "**NARRATOR:**",
      "First paragraph.",
      "",
      "**[VISUAL: Cut to a chart.]**",
      "",
      "Second paragraph.",
      "",
      "**[VISUAL: Cut again.]**",
      "",
      "Third paragraph.",
      "",
    ].join("\n");

    const rawTtsScript = [
      "[TONE: measured]",
      "First paragraph.",
      "[PAUSE: 0.5s]",
      "",
      "[TONE: measured]",
      "Second paragraph.",
      "[PAUSE: 0.5s]",
      "",
      "[TONE: measured]",
      "Third paragraph.",
      "",
    ].join("\n");

    const output = buildCanonicalTtsScript(
      mainScript,
      rawTtsScript,
      [{ id: "main_section", label: "Main Section" }],
    );

    expect(output).toContain("First paragraph.");
    expect(output).toContain("Second paragraph.");
    expect(output).toContain("Third paragraph.");
    expect(output.match(/\[TONE: measured\]/g)).toHaveLength(3);
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
    expect(output).toContain("[INSTRUCT:");
    expect(output).toContain("This is the only line.");
  });
});
