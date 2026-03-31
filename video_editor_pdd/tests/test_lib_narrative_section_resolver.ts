import {
  buildNarrativeStructureManifest,
  groupScriptSectionsByProjectSection,
  parseTimedNarrativeHeadings,
  resolveNarrativeSectionAssignments,
} from "../lib/narration-manifest";

describe("lib/narrative-section-resolver", () => {
  const projectSections = [
    { id: "cold_open", label: "Cold Open" },
    { id: "part1_economics", label: "Part 1: Economics of Darning" },
    { id: "closing", label: "Closing" },
  ];

  it("folds unmatched timed headings into the previous matched project section", () => {
    const headings = [
      { heading: "COLD OPEN: THE SOCK HOOK (0:00 - 2:00)" },
      { heading: "THE THIRTY-SECOND DEMO (2:00 - 2:30)" },
      { heading: "PART 1: THE ECONOMICS OF DARNING (2:30 - 8:30)" },
    ];

    const assignments = resolveNarrativeSectionAssignments(
      headings,
      projectSections,
    );

    expect(assignments).toEqual([
      expect.objectContaining({
        heading: "COLD OPEN: THE SOCK HOOK (0:00 - 2:00)",
        pipelineSectionId: "cold_open",
        matchSource: "fuzzy",
      }),
      expect.objectContaining({
        heading: "THE THIRTY-SECOND DEMO (2:00 - 2:30)",
        pipelineSectionId: "cold_open",
        matchSource: "fold_previous",
      }),
      expect.objectContaining({
        heading: "PART 1: THE ECONOMICS OF DARNING (2:30 - 8:30)",
        pipelineSectionId: "part1_economics",
        matchSource: "fuzzy",
      }),
    ]);
  });

  it("prefers explicit scriptHeadings metadata over fold heuristics", () => {
    const headings = [
      { heading: "COLD OPEN: THE SOCK HOOK (0:00 - 2:00)" },
      { heading: "THE THIRTY-SECOND DEMO (2:00 - 2:30)" },
      { heading: "PART 1: THE ECONOMICS OF DARNING (2:30 - 8:30)" },
    ];

    const assignments = resolveNarrativeSectionAssignments(headings, [
      {
        id: "cold_open",
        label: "Cold Open",
        scriptHeadings: [
          "COLD OPEN: THE SOCK HOOK (0:00 - 2:00)",
          "THE THIRTY-SECOND DEMO (2:00 - 2:30)",
        ],
      },
      ...projectSections.slice(1),
    ]);

    expect(assignments[1]).toEqual(
      expect.objectContaining({
        pipelineSectionId: "cold_open",
        matchSource: "explicit",
      }),
    );
  });

  it("groups parsed script sections by owning project section while preserving folded subsections", () => {
    const mainScript = [
      "## COLD OPEN: THE SOCK HOOK (0:00 - 2:00)",
      "",
      "**NARRATOR:**",
      "Cold open line.",
      "",
      "## THE THIRTY-SECOND DEMO (2:00 - 2:30)",
      "",
      "**NARRATOR:**",
      "Watch this.",
      "",
      "## PART 1: THE ECONOMICS OF DARNING (2:30 - 8:30)",
      "",
      "**NARRATOR:**",
      "This isn't nostalgia.",
      "",
    ].join("\n");

    const grouped = groupScriptSectionsByProjectSection(
      parseTimedNarrativeHeadings(mainScript),
      projectSections,
    );

    expect(grouped.get("cold_open")?.map((section) => section.heading)).toEqual([
      "COLD OPEN: THE SOCK HOOK (0:00 - 2:00)",
      "THE THIRTY-SECOND DEMO (2:00 - 2:30)",
    ]);
    expect(
      grouped.get("part1_economics")?.map((section) => section.heading),
    ).toEqual(["PART 1: THE ECONOMICS OF DARNING (2:30 - 8:30)"]);
  });

  it("uses the canonical narrative structure manifest when grouping sections", () => {
    const mainScript = [
      "## COLD OPEN: THE SOCK HOOK (0:00 - 2:00)",
      "",
      "**NARRATOR:**",
      "Cold open line.",
      "",
      "## THE THIRTY-SECOND DEMO (2:00 - 2:30)",
      "",
      "**NARRATOR:**",
      "Watch this.",
      "",
      "## PART 1: THE ECONOMICS OF DARNING (2:30 - 8:30)",
      "",
      "**NARRATOR:**",
      "This isn't nostalgia.",
      "",
    ].join("\n");

    const parsed = parseTimedNarrativeHeadings(mainScript);
    const manifest = buildNarrativeStructureManifest(mainScript, projectSections);
    const grouped = groupScriptSectionsByProjectSection(
      parsed,
      projectSections,
      manifest,
    );

    expect(grouped.get("cold_open")?.map((section) => section.heading)).toEqual([
      "COLD OPEN: THE SOCK HOOK (0:00 - 2:00)",
      "THE THIRTY-SECOND DEMO (2:00 - 2:30)",
    ]);
  });
});
