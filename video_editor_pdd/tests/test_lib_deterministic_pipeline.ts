import fs from "fs";
import os from "os";
import path from "path";

import {
  applyDeterministicRemotionFix,
  applyDeterministicVideoOverlay,
  buildDeterministicTtsScript,
  generateDeterministicVeoClip,
  writeDeterministicComponent,
  writeDeterministicSectionConstants,
  writeDeterministicSpecsForSection,
} from "../lib/deterministic-pipeline";

jest.mock("../lib/projects", () => ({
  getAppRemotionSrcDir: jest.fn(() => ""),
}));

import { getAppRemotionSrcDir } from "../lib/projects";

describe("lib/deterministic-pipeline", () => {
  let tmpDir: string;
  const mockGetAppRemotionSrcDir = getAppRemotionSrcDir as jest.MockedFunction<typeof getAppRemotionSrcDir>;

  beforeEach(() => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "deterministic-pipeline-"));
    mockGetAppRemotionSrcDir.mockReset();
    mockGetAppRemotionSrcDir.mockReturnValue("");
  });

  afterEach(() => {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  });

  it("buildDeterministicTtsScript preserves section headings and adds annotation tags", () => {
    const mainScript = [
      "## Animation Section",
      "",
      "**NARRATOR:**",
      "This is the first narrated paragraph.",
      "",
      "**NARRATOR:**",
      "This is the second narrated paragraph.",
      "",
      "## Veo Section",
      "",
      "**NARRATOR:**",
      "This is the veo paragraph.",
      "",
    ].join("\n");

    const output = buildDeterministicTtsScript(mainScript, [
      { id: "animation_section", label: "Animation Section" },
      { id: "veo_section", label: "Veo Section" },
    ]);

    expect(output).toContain("## Animation Section");
    expect(output).toContain("## Veo Section");
    expect(output).toContain("[TONE: explanatory]");
    expect(output).toContain("[PACE: moderate]");
    expect(output).toContain("[EMOTION: calm]");
    expect(output).toContain("[PAUSE: 1.0s]");
    expect(output).toContain("This is the first narrated paragraph.");
    expect(output).toContain("This is the veo paragraph.");
  });

  it("keeps folded timed demo headings under the owning canonical section in deterministic mode", () => {
    const mainScript = [
      "## COLD OPEN: THE SOCK HOOK (0:00 - 2:00)",
      "",
      "**NARRATOR:**",
      "If you use Cursor...",
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

    const output = buildDeterministicTtsScript(mainScript, [
      { id: "cold_open", label: "Cold Open" },
      { id: "part1_economics", label: "Part 1: Economics of Darning" },
    ]);

    expect(output).toContain("## Cold Open");
    expect(output).toContain("### THE THIRTY-SECOND DEMO (2:00 - 2:30)");
    expect(output).toContain("Watch this.");

    const part1Block = output.split("## Part 1: Economics of Darning")[1] ?? "";
    expect(part1Block).not.toContain("Watch this.");
  });

  it("writeDeterministicSpecsForSection creates remotion and veo spec files", () => {
    const files = writeDeterministicSpecsForSection(
      tmpDir,
      {
        id: "veo_section",
        label: "Veo Section",
        specDir: "veo_section",
      },
    );

    expect(files).toHaveLength(5);
    expect(fs.existsSync(path.join(tmpDir, "specs", "veo_section", "01_title_card.md"))).toBe(true);
    expect(fs.readFileSync(path.join(tmpDir, "specs", "veo_section", "04_veo_broll.md"), "utf-8"))
      .toMatch(/^\[veo:/);
    expect(fs.readFileSync(path.join(tmpDir, "specs", "veo_section", "03_split_summary.md"), "utf-8"))
      .toMatch(/^\[split:/);
    expect(fs.existsSync(path.join(tmpDir, "specs", "veo_section", "veo.json"))).toBe(true);
  });

  it("writeDeterministicComponent writes a valid flat TSX component", () => {
    const outPath = writeDeterministicComponent(
      path.join(tmpDir, "remotion", "src", "remotion"),
      "animation_section_01_title_card",
      "[title:]\n# Title",
    );

    const source = fs.readFileSync(outPath, "utf-8");
    expect(source).toContain('export const AnimationSection01TitleCard');
    expect(source).toContain('export default AnimationSection01TitleCard');
    expect(source).toContain('AbsoluteFill');
  });

  it("writeDeterministicSectionConstants writes BEATS and VISUAL_SEQUENCE entries", () => {
    const outPath = writeDeterministicSectionConstants(
      tmpDir,
      {
        id: "animation_section",
        specDir: "animation_section",
        compositionId: "AnimationSection",
        durationSeconds: 12,
      },
      ["animation_section_01_title_card", "animation_section_02_key_visual"],
    );

    const source = fs.readFileSync(outPath, "utf-8");
    expect(source).toContain("export const BEATS");
    expect(source).toContain('id: "animation_section_01_title_card"');
    expect(source).toContain('id: "animation_section_02_key_visual"');
    expect(source).toContain("export const VISUAL_SEQUENCE");
  });

  it("generateDeterministicVeoClip creates a playable mp4 file", () => {
    const outPath = path.join(tmpDir, "outputs", "veo", "veo_section.mp4");

    generateDeterministicVeoClip(outPath);

    expect(fs.existsSync(outPath)).toBe(true);
    expect(fs.statSync(outPath).size).toBeGreaterThan(0);
  });

  it("applyDeterministicRemotionFix rewrites section-scoped background colors", () => {
    const remotionDir = path.join(tmpDir, "remotion", "src", "remotion");
    fs.mkdirSync(remotionDir, { recursive: true });
    const targetFile = path.join(remotionDir, "animation_section_01_title_card.tsx");
    fs.writeFileSync(
      targetFile,
      'export const Demo = () => <div style={{ backgroundColor: "#0A1628", background: "#111827" }} />;',
    );

    const modified = applyDeterministicRemotionFix(
      tmpDir,
      "animation_section",
      "Change the background color to bright red (#FF0000).",
    );

    expect(modified).toContain(targetFile);
    const updated = fs.readFileSync(targetFile, "utf-8");
    expect(updated).toContain('backgroundColor: "#FF0000"');
    expect(updated).toContain('background: "#FF0000"');
  });

  it("applyDeterministicRemotionFix rewrites nested directory-based section components", () => {
    const componentDir = path.join(
      tmpDir,
      "remotion",
      "src",
      "remotion",
      "VeoSection11VeoBadgeReprise",
    );
    fs.mkdirSync(componentDir, { recursive: true });
    const targetFile = path.join(componentDir, "VeoSection11VeoBadgeReprise.tsx");
    fs.writeFileSync(
      targetFile,
      'export const Demo = () => <div style={{ backgroundColor: "#0A1628" }} />;',
    );

    const modified = applyDeterministicRemotionFix(
      tmpDir,
      "veo_section",
      "Change the background color to bright green (#00FF00).",
    );

    expect(modified).toContain(targetFile);
    const updated = fs.readFileSync(targetFile, "utf-8");
    expect(updated).toContain('backgroundColor: "#00FF00"');
  });

  it("applyDeterministicRemotionFix falls back to the app remotion source when the project workspace has no remotion tree", () => {
    const appRemotionDir = path.join(tmpDir, "app-remotion");
    const componentDir = path.join(appRemotionDir, "animation_section");
    fs.mkdirSync(componentDir, { recursive: true });
    const targetFile = path.join(componentDir, "Card.tsx");
    fs.writeFileSync(
      targetFile,
      'export const Demo = () => <div style={{ backgroundColor: "#0A1628" }} />;',
    );
    mockGetAppRemotionSrcDir.mockReturnValue(appRemotionDir);

    const modified = applyDeterministicRemotionFix(
      path.join(tmpDir, "project-only"),
      "animation_section",
      "Change the background color to bright yellow (#FFFF00).",
    );

    expect(modified).toContain(targetFile);
    expect(fs.readFileSync(targetFile, "utf-8")).toContain('backgroundColor: "#FFFF00"');
  });

  it("applyDeterministicVideoOverlay rewrites the mp4 with a visible video filter", () => {
    const outPath = path.join(tmpDir, "outputs", "sections", "animation_section.mp4");
    generateDeterministicVeoClip(outPath);
    const beforeSize = fs.statSync(outPath).size;

    applyDeterministicVideoOverlay(outPath, "#FF0000");

    expect(fs.existsSync(outPath)).toBe(true);
    expect(fs.statSync(outPath).mtimeMs).toBeGreaterThan(0);
    expect(fs.statSync(outPath).size).toBeGreaterThan(0);
    expect(fs.statSync(outPath).size).not.toBe(beforeSize);
  });
});
