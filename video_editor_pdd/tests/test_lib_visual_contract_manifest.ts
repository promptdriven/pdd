import fs from "fs";
import os from "os";
import path from "path";

import {
  loadVisualContractManifest,
  resolveSectionVisualContract,
} from "../app/api/pipeline/_lib/visual-contract-manifest";

jest.mock("@/lib/projects", () => ({
  getProjectDir: () => process.cwd(),
}));

describe("visual-contract-manifest extended fields", () => {
  let tmpDir: string;
  let originalCwd: string;

  beforeEach(() => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "visual-contract-"));
    originalCwd = process.cwd();
    process.chdir(tmpDir);
  });

  afterEach(() => {
    process.chdir(originalCwd);
    fs.rmSync(tmpDir, { recursive: true, force: true });
  });

  function writeManifest(sections: unknown[]) {
    const dir = path.join(tmpDir, "outputs", "compositions");
    fs.mkdirSync(dir, { recursive: true });
    fs.writeFileSync(
      path.join(dir, "visual-manifest.json"),
      JSON.stringify({ version: 1, updatedAt: new Date().toISOString(), sections })
    );
  }

  it("exposes coverSegments from manifest", () => {
    writeManifest([
      {
        id: "cold_open",
        visuals: [
          {
            id: "cold_open_01_title",
            specBaseName: "01_title",
            coverSegments: ["cold_open_001", "cold_open_002"],
          },
        ],
      },
    ]);

    const visual = resolveSectionVisualContract("cold_open", "01_title");
    expect(visual).not.toBeNull();
    expect(visual!.coverSegments).toEqual(["cold_open_001", "cold_open_002"]);
  });

  it("exposes parentId and children from manifest", () => {
    writeManifest([
      {
        id: "cold_open",
        visuals: [
          {
            id: "cold_open_01_split",
            specBaseName: "01_split",
            children: ["cold_open_02_veo"],
          },
          {
            id: "cold_open_02_veo",
            specBaseName: "02_veo",
            parentId: "cold_open_01_split",
          },
        ],
      },
    ]);

    const parent = resolveSectionVisualContract("cold_open", "01_split");
    const child = resolveSectionVisualContract("cold_open", "02_veo");

    expect(parent!.children).toEqual(["cold_open_02_veo"]);
    expect(child!.parentId).toBe("cold_open_01_split");
  });

  it("exposes laneHint from manifest", () => {
    writeManifest([
      {
        id: "demo",
        visuals: [
          {
            id: "demo_01_bg",
            specBaseName: "01_bg",
            laneHint: "background",
          },
        ],
      },
    ]);

    const visual = resolveSectionVisualContract("demo", "01_bg");
    expect(visual!.laneHint).toBe("background");
  });

  it("tolerates missing new fields (legacy manifest)", () => {
    writeManifest([
      {
        id: "intro",
        visuals: [
          {
            id: "intro_01_card",
            specBaseName: "01_card",
          },
        ],
      },
    ]);

    const visual = resolveSectionVisualContract("intro", "01_card");
    expect(visual).not.toBeNull();
    expect(visual!.coverSegments).toBeUndefined();
    expect(visual!.parentId).toBeUndefined();
    expect(visual!.children).toBeUndefined();
    expect(visual!.laneHint).toBeUndefined();
  });
});
