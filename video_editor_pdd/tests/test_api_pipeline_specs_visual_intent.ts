const mockRegisterExecutor = jest.fn();
const mockRunClaudeFix = jest.fn();
const mockLoadProject = jest.fn();

const mockExistsSync = jest.fn();
const mockReadFileSync = jest.fn();
const mockRmSync = jest.fn();
const mockMkdirSync = jest.fn();
const mockWriteFileSync = jest.fn();

jest.mock("@/lib/jobs", () => ({
  registerExecutor: (...args: unknown[]) => mockRegisterExecutor(...args),
  runPipelineStage: jest.fn(),
}));

jest.mock("@/lib/claude", () => ({
  runClaudeFix: (...args: unknown[]) => mockRunClaudeFix(...args),
}));

jest.mock("@/lib/project", () => ({
  loadProject: (...args: unknown[]) => mockLoadProject(...args),
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
  },
  existsSync: (...args: unknown[]) => mockExistsSync(...args),
  readFileSync: (...args: unknown[]) => mockReadFileSync(...args),
  rmSync: (...args: unknown[]) => mockRmSync(...args),
  mkdirSync: (...args: unknown[]) => mockMkdirSync(...args),
  writeFileSync: (...args: unknown[]) => mockWriteFileSync(...args),
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
    mockExistsSync.mockReset();
    mockReadFileSync.mockReset();
    mockRmSync.mockReset();
    mockMkdirSync.mockReset();
    mockWriteFileSync.mockReset();

    mockLoadProject.mockReturnValue(mockProjectConfig());
    mockRunClaudeFix.mockResolvedValue(undefined);

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
});
