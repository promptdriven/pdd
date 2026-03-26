import fs from "fs";

jest.mock("fs", () => ({
  __esModule: true,
  default: {
    existsSync: jest.fn(),
  },
  existsSync: jest.fn(),
}));

import { resolvePythonRunSpec } from "@/app/api/pipeline/_lib/python-runtime";

const mockExistsSync = jest.mocked(fs.existsSync);

describe("resolvePythonRunSpec", () => {
  const originalEnv = process.env;

  beforeEach(() => {
    jest.resetAllMocks();
    process.env = { ...originalEnv };
  });

  afterAll(() => {
    process.env = originalEnv;
  });

  it("prefers an explicit python executable override", () => {
    process.env.PIPELINE_PYTHON_EXECUTABLE = "/custom/python";
    mockExistsSync.mockImplementation((p: fs.PathLike) => String(p) === "/custom/python");

    const result = resolvePythonRunSpec({ preferredCondaEnv: "video_editor" });

    expect(result.command).toBe("/custom/python");
    expect(result.argsPrefix).toEqual([]);
  });

  it("uses the current conda python when already inside the preferred env", () => {
    process.env.CONDA_DEFAULT_ENV = "video_editor";
    process.env.CONDA_PREFIX = "/envs/video_editor";
    mockExistsSync.mockImplementation(
      (p: fs.PathLike) => String(p) === "/envs/video_editor/bin/python"
    );

    const result = resolvePythonRunSpec({ preferredCondaEnv: "video_editor" });

    expect(result.command).toBe("/envs/video_editor/bin/python");
    expect(result.argsPrefix).toEqual([]);
  });

  it("uses conda run for the preferred env when the current env differs", () => {
    process.env.CONDA_DEFAULT_ENV = "base";
    process.env.CONDA_PREFIX = "/envs/base";
    process.env.CONDA_EXE = "/opt/miniforge/bin/conda";
    mockExistsSync.mockImplementation(
      (p: fs.PathLike) => String(p) === "/opt/miniforge/bin/conda"
    );

    const result = resolvePythonRunSpec({ preferredCondaEnv: "video_editor" });

    expect(result.command).toBe("/opt/miniforge/bin/conda");
    expect(result.argsPrefix).toEqual([
      "run",
      "--no-capture-output",
      "-n",
      "video_editor",
      "python",
    ]);
  });

  it("falls back to the current conda python when no preferred env runner is available", () => {
    process.env.CONDA_DEFAULT_ENV = "pdd";
    process.env.CONDA_PREFIX = "/envs/pdd";
    mockExistsSync.mockImplementation(
      (p: fs.PathLike) => String(p) === "/envs/pdd/bin/python"
    );

    const result = resolvePythonRunSpec({ preferredCondaEnv: "video_editor" });

    expect(result.command).toBe("/envs/pdd/bin/python");
    expect(result.argsPrefix).toEqual([]);
  });

  it("sanitizes PYTHONPATH and enables PYTHONNOUSERSITE", () => {
    process.env.PYTHONPATH = "/tmp/custom";
    process.env.PYTHONNOUSERSITE = "";
    mockExistsSync.mockReturnValue(false);

    const result = resolvePythonRunSpec({ preferredCondaEnv: "video_editor" });

    expect(result.env.PYTHONNOUSERSITE).toBe("1");
    expect(result.env.PYTHONPATH).toBeUndefined();
  });

  it("falls back to bare python3 when no env-specific python is available", () => {
    mockExistsSync.mockReturnValue(false);

    const result = resolvePythonRunSpec({ preferredCondaEnv: "video_editor" });

    expect(result.command).toBe("python3");
    expect(result.argsPrefix).toEqual([]);
  });
});
