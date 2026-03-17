const mockRegisterExecutor = jest.fn();
const mockRunClaudeFix = jest.fn();
const mockLoadProject = jest.fn();
const mockSaveProject = jest.fn();

const mockExistsSync = jest.fn();
const mockReadFileSync = jest.fn();
const mockRmSync = jest.fn();
const mockMkdirSync = jest.fn();
const mockWriteFileSync = jest.fn();
const mockReaddirSync = jest.fn();

jest.mock("@/lib/jobs", () => ({
  registerExecutor: (...args: unknown[]) => mockRegisterExecutor(...args),
  runPipelineStage: jest.fn(),
}));

jest.mock("@/lib/claude", () => ({
  runClaudeFix: (...args: unknown[]) => mockRunClaudeFix(...args),
}));

jest.mock("@/lib/project", () => ({
  loadProject: (...args: unknown[]) => mockLoadProject(...args),
  saveProject: (...args: unknown[]) => mockSaveProject(...args),
}));

jest.mock("@/lib/deterministic-pipeline", () => ({
  isDeterministicPipelineMode: () => false,
  writeDeterministicSpecsForSection: jest.fn(),
}));

jest.mock("fs", () => ({
  __esModule: true,
  default: {
    existsSync: (...args: unknown[]) => mockExistsSync(...args),
    readFileSync: (...args: unknown[]) => mockReadFileSync(...args),
    rmSync: (...args: unknown[]) => mockRmSync(...args),
    mkdirSync: (...args: unknown[]) => mockMkdirSync(...args),
    writeFileSync: (...args: unknown[]) => mockWriteFileSync(...args),
    readdirSync: (...args: unknown[]) => mockReaddirSync(...args),
  },
  existsSync: (...args: unknown[]) => mockExistsSync(...args),
  readFileSync: (...args: unknown[]) => mockReadFileSync(...args),
  rmSync: (...args: unknown[]) => mockRmSync(...args),
  mkdirSync: (...args: unknown[]) => mockMkdirSync(...args),
  writeFileSync: (...args: unknown[]) => mockWriteFileSync(...args),
  readdirSync: (...args: unknown[]) => mockReaddirSync(...args),
}));

import "../app/api/pipeline/specs/run/route";

const registerCallArgs = {
  stage: mockRegisterExecutor.mock.calls[0]?.[0] as string,
  factory: mockRegisterExecutor.mock.calls[0]?.[1] as (
    params: Record<string, unknown>,
    send: Function
  ) => (onLog: (msg: string) => void) => Promise<void>,
};

function mockProjectConfig() {
  return {
    sections: [
      {
        id: "animation_section",
        label: "Animation Section",
        specDir: "animation_section",
      },
      {
        id: "veo_section",
        label: "Veo Section",
        specDir: "veo_section",
      },
      {
        id: "cinematic_section",
        label: "Cinematic Section",
        specDir: "cinematic_section",
      },
    ],
    veo: { defaultAspectRatio: "16:9" },
  };
}

describe("specs route visual-intent prompting", () => {
  beforeEach(() => {
    mockRunClaudeFix.mockReset();
    mockLoadProject.mockReset();
    mockSaveProject.mockReset();
    mockExistsSync.mockReset();
    mockReadFileSync.mockReset();
    mockRmSync.mockReset();
    mockMkdirSync.mockReset();
    mockWriteFileSync.mockReset();
    mockReaddirSync.mockReset();

    mockLoadProject.mockReturnValue(mockProjectConfig());
    mockRunClaudeFix.mockResolvedValue(undefined);
    mockSaveProject.mockReturnValue(undefined);
    mockReaddirSync.mockReturnValue([]);

    mockExistsSync.mockImplementation((filePath: string) => {
      return typeof filePath === "string" && filePath.includes("narrative/main_script.md");
    });

    mockReadFileSync.mockImplementation((filePath: string) => {
      if (typeof filePath !== "string") {
        return "";
      }
      if (filePath.includes("narrative/main_script.md")) {
        return `
## Animation Section
**[VISUAL: Animated chart with axes and labels.]**
[Remotion] Build an animated chart.

## Veo Section
[veo: Ocean wave at sunset]

## Cinematic Section
**[VISUAL: A developer at a keyboard in a dim office while rain streaks the window.]**
**[VISUAL: Close-up on hands typing. Hard cut to a city street at night.]**
        `.trim();
      }
      return "";
    });
  });

  it("registers the specs executor", () => {
    expect(registerCallArgs.stage).toBe("specs");
  });

  it("tells Claude to keep a diagrammatic section mostly remotion-based", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const animationPrompt = mockRunClaudeFix.mock.calls[0][0];
    expect(animationPrompt).toContain(
      "This section appears primarily abstract, diagrammatic, or UI-driven based on main_script.md."
    );
    expect(animationPrompt).toContain("Avoid [veo:] unless a beat clearly requires cinematic footage.");
  });

  it("preserves veo generation guidance for a script section that includes veo footage", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const veoPrompt = mockRunClaudeFix.mock.calls[1][0];
    expect(veoPrompt).toContain("This section explicitly includes [veo:] footage in main_script.md.");
  });

  it("tells Claude to decide scene-by-scene and include veo for inferred cinematic sections", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const cinematicPrompt = mockRunClaudeFix.mock.calls[2][0];
    expect(cinematicPrompt).toContain(
      "This section includes cinematic or live-action beats in main_script.md even without explicit [veo:] markers."
    );
    expect(cinematicPrompt).toContain(
      "Decide scene-by-scene whether each beat is better as [veo:], [Remotion], [title:], or [split:]."
    );
    expect(cinematicPrompt).toContain("Include at least one [veo:] spec for the cinematic beats.");
  });

  it("scales the Claude timeout for larger section contexts", async () => {
    mockExistsSync.mockImplementation((filePath: string) => {
      if (typeof filePath !== "string") return false;
      return (
        filePath.includes("narrative/main_script.md") ||
        filePath.includes("specs/animation_section/spec.md")
      );
    });
    mockReadFileSync.mockImplementation((filePath: string) => {
      if (typeof filePath !== "string") {
        return "";
      }
      if (filePath.includes("narrative/main_script.md")) {
        return `
## Animation Section
**[VISUAL: Animated chart with axes and labels.]**
**NARRATOR:**
${"A".repeat(24_000)}
        `.trim();
      }
      if (filePath.includes("specs/animation_section/spec.md")) {
        return `Narrative arc\n\n${"B".repeat(18_000)}`;
      }
      return "";
    });

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const animationCall = mockRunClaudeFix.mock.calls.find((call) =>
      String(call[0]).includes("specs/animation_section/")
    );
    expect(animationCall).toBeDefined();
    expect(animationCall?.[3]?.timeoutMs).toBeGreaterThan(600_000);
    expect(animationCall?.[3]?.timeoutMs).toBeLessThanOrEqual(1_500_000);
  });

  it("adds extra timeout budget for hybrid sections with many visual beats", async () => {
    mockLoadProject.mockReturnValue({
      sections: [
        {
          id: "dense_hybrid_section",
          label: "Dense Hybrid Section",
          specDir: "dense_hybrid_section",
        },
      ],
      veo: { defaultAspectRatio: "16:9" },
    });
    mockExistsSync.mockImplementation((filePath: string) => {
      if (typeof filePath !== "string") return false;
      return filePath.includes("narrative/main_script.md");
    });
    mockReadFileSync.mockImplementation((filePath: string) => {
      if (typeof filePath !== "string") {
        return "";
      }
      if (filePath.includes("narrative/main_script.md")) {
        return `
## Dense Hybrid Section
${Array.from({ length: 20 }, (_, index) => `**[VISUAL: Developer in a rainy office close-up beat ${index + 1}.]**`).join("\n")}
**[VISUAL: A chart overlay appears with annotations and graph axes.]**
**NARRATOR:**
${"A".repeat(8000)}
        `.trim();
      }
      return "";
    });

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    expect(mockRunClaudeFix).toHaveBeenCalledTimes(1);
    expect(mockRunClaudeFix.mock.calls[0]?.[3]?.timeoutMs).toBeGreaterThan(840_000);
  });

  it("adds extra timeout budget for remotion-only sections with many visual beats", async () => {
    mockLoadProject.mockReturnValue({
      sections: [
        {
          id: "dense_remotion_section",
          label: "Dense Remotion Section",
          specDir: "dense_remotion_section",
        },
      ],
      veo: { defaultAspectRatio: "16:9" },
    });
    mockExistsSync.mockImplementation((filePath: string) => {
      if (typeof filePath !== "string") return false;
      return filePath.includes("narrative/main_script.md");
    });
    mockReadFileSync.mockImplementation((filePath: string) => {
      if (typeof filePath !== "string") {
        return "";
      }
      if (filePath.includes("narrative/main_script.md")) {
        return `
## Dense Remotion Section
${Array.from(
  { length: 14 },
  (_, index) =>
    `**[VISUAL: Graph beat ${index + 1} with axis labels, curve overlays, and terminal annotations.]**`
).join("\n")}
**NARRATOR:**
${"A".repeat(6000)}
        `.trim();
      }
      return "";
    });

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    expect(mockRunClaudeFix).toHaveBeenCalledTimes(1);
    expect(mockRunClaudeFix.mock.calls[0]?.[3]?.timeoutMs).toBeGreaterThan(630_000);
  });

  it("adds a fixed finalization buffer for lighter sections so Claude can finish after the last write", async () => {
    mockLoadProject.mockReturnValue({
      sections: [
        {
          id: "lighter_section",
          label: "Lighter Section",
          specDir: "lighter_section",
        },
      ],
      veo: { defaultAspectRatio: "16:9" },
    });
    mockExistsSync.mockImplementation((filePath: string) => {
      if (typeof filePath !== "string") return false;
      return filePath.includes("narrative/main_script.md");
    });
    mockReadFileSync.mockImplementation((filePath: string) => {
      if (typeof filePath !== "string") {
        return "";
      }
      if (filePath.includes("narrative/main_script.md")) {
        return `
## Lighter Section
**[VISUAL: Clean title card.]**
**NARRATOR:**
A short narration block.
        `.trim();
      }
      return "";
    });

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    expect(mockRunClaudeFix).toHaveBeenCalledTimes(1);
    expect(mockRunClaudeFix.mock.calls[0]?.[3]?.timeoutMs).toBe(660_000);
  });

  it("continues later sections after a section times out and reports an aggregated error", async () => {
    mockRunClaudeFix.mockImplementation(async (prompt: string) => {
      if (prompt.includes("specs/veo_section/")) {
        throw new Error("Claude CLI timeout after 600s");
      }
    });

    const onLog = jest.fn();
    const executor = registerCallArgs.factory({}, jest.fn());

    await expect(executor(onLog)).rejects.toThrow(
      "Spec generation failed for 1 section(s): veo_section (Claude CLI timeout after 600s)"
    );

    const generatedSections = mockRunClaudeFix.mock.calls.map((call) => {
      const prompt = String(call[0]);
      const match = prompt.match(/specs\/([^/]+)\//);
      return match?.[1] ?? "unknown";
    });
    expect(generatedSections).toEqual(
      expect.arrayContaining(["animation_section", "veo_section", "cinematic_section"])
    );
    expect(onLog).toHaveBeenCalledWith(
      "[specs] Section veo_section failed (67%): Claude CLI timeout after 600s"
    );
    expect(onLog).toHaveBeenCalledWith(
      "[specs] Spec generation failed for 1 section(s): veo_section (Claude CLI timeout after 600s)"
    );
  });

  it("syncs inferred recurring Veo references into project.json after a successful run", async () => {
    mockExistsSync.mockImplementation((filePath: string) => {
      if (typeof filePath !== "string") return false;
      return (
        filePath.includes("narrative/main_script.md") ||
        filePath.includes("specs/veo_section") ||
        filePath.includes("specs/cinematic_section")
      );
    });
    mockReaddirSync.mockImplementation((filePath: string) => {
      if (typeof filePath !== "string") return [];
      if (filePath.includes("specs/veo_section")) {
        return ["01_grandmother_intro.md"];
      }
      if (filePath.includes("specs/cinematic_section")) {
        return ["02_grandmother_callback.md"];
      }
      return [];
    });
    mockReadFileSync.mockImplementation((filePath: string) => {
      if (typeof filePath !== "string") {
        return "";
      }
      if (filePath.includes("narrative/main_script.md")) {
        return `
## Animation Section
**[VISUAL: Animated chart with axes and labels.]**

## Veo Section
**[VISUAL: A grandmother under a lamp, threading a needle.]**

## Cinematic Section
**[VISUAL: The same grandmother sets down the sock and smiles faintly.]**
        `.trim();
      }
      if (filePath.includes("01_grandmother_intro.md")) {
        return [
          "[veo:]",
          "",
          "### Veo Prompt",
          "```",
          "Warm portrait of a 1950s grandmother under a tungsten lamp.",
          "```",
          "",
          "## Data Points",
          "```json",
          "{",
          '  "type": "veo_clip",',
          '  "clipId": "grandmother_intro",',
          '  "characters": [',
          '    {',
          '      "id": "grandmother",',
          '      "label": "Grandmother",',
          '      "referencePrompt": "Portrait photo of the same 1950s grandmother, warm lamp light, lace curtains behind her."',
          '    }',
          "  ]",
          "}",
          "```",
        ].join("\n");
      }
      if (filePath.includes("02_grandmother_callback.md")) {
        return [
          "[veo:]",
          "",
          "### Veo Prompt",
          "```",
          "The same grandmother pauses and sets down a sock.",
          "```",
          "",
          "## Data Points",
          "```json",
          "{",
          '  "type": "veo_clip",',
          '  "clipId": "grandmother_callback",',
          '  "characters": [',
          '    {',
          '      "id": "grandmother",',
          '      "label": "Grandmother",',
          '      "referencePrompt": "Portrait photo of the same 1950s grandmother, warm lamp light, lace curtains behind her."',
          '    }',
          "  ]",
          "}",
          "```",
        ].join("\n");
      }
      return "";
    });

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    expect(mockSaveProject).toHaveBeenCalledTimes(1);
    const savedConfig = mockSaveProject.mock.calls[0][0];
    expect(savedConfig.veo.references).toEqual([
      expect.objectContaining({
        id: "grandmother",
        label: "Grandmother",
        imagePath: "outputs/veo/references/grandmother.png",
        sections: ["cinematic_section", "veo_section"],
        referencePrompt:
          "Portrait photo of the same 1950s grandmother, warm lamp light, lace curtains behind her.",
        source: "stage6-inferred",
      }),
    ]);
  });
});
