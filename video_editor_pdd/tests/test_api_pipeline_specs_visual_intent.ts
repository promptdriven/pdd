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
[Remotion] Build an animated chart.

## Veo Section
[veo: Ocean wave at sunset]
        `.trim();
      }
      return "";
    });
  });

  it("registers the specs executor", () => {
    expect(registerCallArgs.stage).toBe("specs");
  });

  it("tells Claude not to generate veo specs for a non-veo script section", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const animationPrompt = mockRunClaudeFix.mock.calls[0][0];
    expect(animationPrompt).toContain("Do NOT create any [veo:] specs for this section.");
  });

  it("preserves veo generation guidance for a script section that includes veo footage", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const veoPrompt = mockRunClaudeFix.mock.calls[1][0];
    expect(veoPrompt).toContain("This section explicitly includes [veo:] footage in main_script.md.");
  });
});
