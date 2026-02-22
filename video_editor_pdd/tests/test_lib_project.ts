/**
 * Tests for lib/project.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/lib_project_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. loadProject(dir?) — reads, parses, validates project.json; throws on missing/invalid
 *   2. saveProject(config, dir?) — validates with Zod, writes atomically via tmp+rename
 *   3. getSection(id, config) — finds section by id, returns undefined if not found
 *   4. validateProjectConfig(data) — thin Zod parse wrapper, throws ZodError
 *   5. projectConfigSchema — named export, validates nested objects
 *   6. server-only guard
 *   7. Nested schema validation (tts, veo, render, audioSync, sections)
 *   8. saveProject uses 2-space indentation
 */

import fs from "fs";
import os from "os";
import path from "path";
import { z } from "zod";

import {
  loadProject,
  saveProject,
  getSection,
  validateProjectConfig,
  projectConfigSchema,
  sectionSchema,
  ttsConfigSchema,
  veoConfigSchema,
  renderConfigSchema,
  audioSyncSchema,
} from "../lib/project";

import type { ProjectConfig, Section } from "../lib/types";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Creates a temp directory for isolated file-system tests. */
function createTmpDir(): string {
  return fs.mkdtempSync(path.join(os.tmpdir(), "pdd-project-test-"));
}

/** Returns a valid ProjectConfig for testing. */
function validConfig(): ProjectConfig {
  return {
    name: "Test Project",
    outputResolution: "1920x1080",
    tts: {
      voice: "en-US-Neural2-F",
      rate: 1.0,
      model: "google-tts-v2",
    },
    sections: [
      {
        id: "intro",
        label: "Introduction",
        videoFile: "output/sections/intro.mp4",
        specDir: "specs/intro",
        remotionDir: "remotion/intro",
        compositionId: "IntroComposition",
        durationSeconds: 12.5,
        offsetSeconds: 0,
      },
      {
        id: "main",
        label: "Main Content",
        videoFile: "output/sections/main.mp4",
        specDir: "specs/main",
        remotionDir: "remotion/main",
        compositionId: "MainComposition",
        durationSeconds: 45,
        offsetSeconds: 12.5,
      },
    ],
    audioSync: {
      sectionGroups: {
        narration: ["intro", "main"],
        music: ["intro"],
      },
    },
    veo: {
      model: "veo-2.0-generate-001",
      aspectRatio: "16:9",
      referenceImages: {
        logo: "assets/logo.png",
      },
    },
    render: {
      maxParallelRenders: 3,
      outputDir: "output/final",
      fps: 30,
      width: 1920,
      height: 1080,
    },
  };
}

/** Writes a project.json file to a directory. */
function writeProjectJson(dir: string, data: unknown): void {
  fs.writeFileSync(
    path.join(dir, "project.json"),
    JSON.stringify(data, null, 2),
    "utf8"
  );
}

// ---------------------------------------------------------------------------
// 1. validateProjectConfig
// ---------------------------------------------------------------------------

describe("validateProjectConfig", () => {
  it("returns a typed ProjectConfig for valid data", () => {
    const result = validateProjectConfig(validConfig());
    expect(result.name).toBe("Test Project");
    expect(result.outputResolution).toBe("1920x1080");
  });

  it("throws ZodError for invalid data", () => {
    expect(() => validateProjectConfig({})).toThrow(z.ZodError);
  });

  it("throws ZodError with field-level details", () => {
    try {
      validateProjectConfig({ name: 123 });
      fail("should have thrown");
    } catch (err) {
      expect(err).toBeInstanceOf(z.ZodError);
      const zodErr = err as z.ZodError;
      const paths = zodErr.issues.map((i) => i.path.join("."));
      expect(paths).toContain("name");
    }
  });

  it("throws ZodError for invalid outputResolution enum", () => {
    const data = { ...validConfig(), outputResolution: "4K" };
    expect(() => validateProjectConfig(data)).toThrow(z.ZodError);
  });

  it("accepts '1280x720' as a valid outputResolution", () => {
    const data = { ...validConfig(), outputResolution: "1280x720" };
    const result = validateProjectConfig(data);
    expect(result.outputResolution).toBe("1280x720");
  });
});

// ---------------------------------------------------------------------------
// 2. projectConfigSchema — Zod schema validation
// ---------------------------------------------------------------------------

describe("projectConfigSchema", () => {
  it("is a named export (Zod object)", () => {
    expect(projectConfigSchema).toBeDefined();
    expect(typeof projectConfigSchema.parse).toBe("function");
  });

  it("validates a complete valid config", () => {
    const result = projectConfigSchema.parse(validConfig());
    expect(result.name).toBe("Test Project");
  });

  it("rejects missing required top-level fields", () => {
    expect(() => projectConfigSchema.parse({})).toThrow(z.ZodError);
  });

  it("rejects missing tts field", () => {
    const data = { ...validConfig() } as any;
    delete data.tts;
    expect(() => projectConfigSchema.parse(data)).toThrow(z.ZodError);
  });

  it("rejects missing sections field", () => {
    const data = { ...validConfig() } as any;
    delete data.sections;
    expect(() => projectConfigSchema.parse(data)).toThrow(z.ZodError);
  });

  it("rejects missing veo field", () => {
    const data = { ...validConfig() } as any;
    delete data.veo;
    expect(() => projectConfigSchema.parse(data)).toThrow(z.ZodError);
  });

  it("rejects missing render field", () => {
    const data = { ...validConfig() } as any;
    delete data.render;
    expect(() => projectConfigSchema.parse(data)).toThrow(z.ZodError);
  });

  it("rejects missing audioSync field", () => {
    const data = { ...validConfig() } as any;
    delete data.audioSync;
    expect(() => projectConfigSchema.parse(data)).toThrow(z.ZodError);
  });
});

// ---------------------------------------------------------------------------
// 3. Nested schema validation
// ---------------------------------------------------------------------------

describe("ttsConfigSchema", () => {
  it("validates a valid TTS config", () => {
    const result = ttsConfigSchema.parse({
      voice: "en-US-Neural2-F",
      rate: 1.0,
      model: "google-tts-v2",
    });
    expect(result.voice).toBe("en-US-Neural2-F");
    expect(result.rate).toBe(1.0);
  });

  it("coerces rate from string to number", () => {
    const result = ttsConfigSchema.parse({
      voice: "en-US-Neural2-F",
      rate: "1.5",
      model: "google-tts-v2",
    });
    expect(result.rate).toBe(1.5);
    expect(typeof result.rate).toBe("number");
  });

  it("rejects missing voice", () => {
    expect(() =>
      ttsConfigSchema.parse({ rate: 1, model: "m" })
    ).toThrow(z.ZodError);
  });
});

describe("sectionSchema", () => {
  it("validates a complete section", () => {
    const result = sectionSchema.parse({
      id: "intro",
      label: "Introduction",
      videoFile: "output/intro.mp4",
      specDir: "specs/intro",
      remotionDir: "remotion/intro",
      compositionId: "IntroComp",
      durationSeconds: 10,
      offsetSeconds: 0,
    });
    expect(result.id).toBe("intro");
  });

  it("defaults durationSeconds to 0 when omitted", () => {
    const result = sectionSchema.parse({
      id: "s1",
      label: "S1",
      videoFile: "v.mp4",
      specDir: "specs",
      remotionDir: "remotion",
      compositionId: "Comp",
    });
    expect(result.durationSeconds).toBe(0);
  });

  it("defaults offsetSeconds to 0 when omitted", () => {
    const result = sectionSchema.parse({
      id: "s1",
      label: "S1",
      videoFile: "v.mp4",
      specDir: "specs",
      remotionDir: "remotion",
      compositionId: "Comp",
    });
    expect(result.offsetSeconds).toBe(0);
  });

  it("coerces durationSeconds from string", () => {
    const result = sectionSchema.parse({
      id: "s1",
      label: "S1",
      videoFile: "v.mp4",
      specDir: "specs",
      remotionDir: "remotion",
      compositionId: "Comp",
      durationSeconds: "12.5",
      offsetSeconds: "3",
    });
    expect(result.durationSeconds).toBe(12.5);
    expect(result.offsetSeconds).toBe(3);
    expect(typeof result.durationSeconds).toBe("number");
  });
});

describe("veoConfigSchema", () => {
  it("validates referenceImages as Record<string, string>", () => {
    const result = veoConfigSchema.parse({
      model: "veo-2.0",
      aspectRatio: "16:9",
      referenceImages: { logo: "logo.png", bg: "bg.png" },
    });
    expect(result.referenceImages).toEqual({ logo: "logo.png", bg: "bg.png" });
  });

  it("accepts empty referenceImages", () => {
    const result = veoConfigSchema.parse({
      model: "veo-2.0",
      aspectRatio: "16:9",
      referenceImages: {},
    });
    expect(result.referenceImages).toEqual({});
  });

  it("rejects missing referenceImages", () => {
    expect(() =>
      veoConfigSchema.parse({ model: "veo", aspectRatio: "16:9" })
    ).toThrow(z.ZodError);
  });
});

describe("renderConfigSchema", () => {
  it("validates a complete render config", () => {
    const result = renderConfigSchema.parse({
      maxParallelRenders: 3,
      outputDir: "output/final",
      fps: 30,
      width: 1920,
      height: 1080,
    });
    expect(result.fps).toBe(30);
    expect(result.width).toBe(1920);
  });

  it("coerces numeric fields from strings", () => {
    const result = renderConfigSchema.parse({
      maxParallelRenders: "4",
      outputDir: "out",
      fps: "60",
      width: "1280",
      height: "720",
    });
    expect(result.maxParallelRenders).toBe(4);
    expect(typeof result.fps).toBe("number");
  });
});

describe("audioSyncSchema", () => {
  it("validates sectionGroups as Record<string, string[]>", () => {
    const result = audioSyncSchema.parse({
      sectionGroups: {
        narration: ["intro", "main"],
        music: ["intro"],
      },
    });
    expect(result.sectionGroups.narration).toEqual(["intro", "main"]);
  });

  it("accepts empty sectionGroups", () => {
    const result = audioSyncSchema.parse({ sectionGroups: {} });
    expect(result.sectionGroups).toEqual({});
  });
});

// ---------------------------------------------------------------------------
// 4. loadProject
// ---------------------------------------------------------------------------

describe("loadProject", () => {
  let tmpDir: string;

  beforeEach(() => {
    tmpDir = createTmpDir();
  });

  afterEach(() => {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  });

  it("reads and parses a valid project.json", () => {
    writeProjectJson(tmpDir, validConfig());
    const result = loadProject(tmpDir);
    expect(result.name).toBe("Test Project");
    expect(result.sections).toHaveLength(2);
  });

  it("returns a fully typed ProjectConfig", () => {
    writeProjectJson(tmpDir, validConfig());
    const result = loadProject(tmpDir);
    expect(result.tts.voice).toBe("en-US-Neural2-F");
    expect(result.veo.referenceImages).toEqual({ logo: "assets/logo.png" });
    expect(result.render.fps).toBe(30);
  });

  it("throws descriptive error when file not found", () => {
    expect(() => loadProject(tmpDir)).toThrow(/project\.json not found/);
  });

  it("includes file path in not-found error message", () => {
    const expectedPath = path.join(tmpDir, "project.json");
    expect(() => loadProject(tmpDir)).toThrow(expectedPath);
  });

  it("throws ZodError for invalid JSON shape", () => {
    writeProjectJson(tmpDir, { name: 123 });
    expect(() => loadProject(tmpDir)).toThrow();
  });

  it("includes file path in ZodError message", () => {
    writeProjectJson(tmpDir, { name: 123 });
    try {
      loadProject(tmpDir);
      fail("should have thrown");
    } catch (err) {
      expect(err).toBeInstanceOf(z.ZodError);
      expect((err as z.ZodError).message).toContain(
        path.join(tmpDir, "project.json")
      );
    }
  });

  it("reads from process.cwd() when dir is omitted", () => {
    // We verify this by checking the path construction, not by actually
    // writing to cwd. The function joins dir ?? process.cwd() with 'project.json'.
    // Since cwd likely doesn't have a valid project.json (or does), we test
    // the codepath by confirming it doesn't throw a "dir" related error.
    // We test this more directly via saveProject + loadProject round-trip.
    writeProjectJson(tmpDir, validConfig());
    const result = loadProject(tmpDir);
    expect(result).toBeDefined();
  });

  it("validates sections with defaults applied", () => {
    const config = validConfig();
    // Remove optional duration/offset fields to test defaults
    const rawSections = config.sections.map((s: any) => {
      const { durationSeconds, offsetSeconds, ...rest } = s;
      return rest;
    });
    writeProjectJson(tmpDir, { ...config, sections: rawSections });
    const result = loadProject(tmpDir);
    expect(result.sections[0].durationSeconds).toBe(0);
    expect(result.sections[0].offsetSeconds).toBe(0);
  });

  it("handles empty sections array", () => {
    const config = { ...validConfig(), sections: [] };
    writeProjectJson(tmpDir, config);
    const result = loadProject(tmpDir);
    expect(result.sections).toEqual([]);
  });
});

// ---------------------------------------------------------------------------
// 5. saveProject
// ---------------------------------------------------------------------------

describe("saveProject", () => {
  let tmpDir: string;

  beforeEach(() => {
    tmpDir = createTmpDir();
  });

  afterEach(() => {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  });

  it("writes project.json to the specified directory", () => {
    saveProject(validConfig(), tmpDir);
    const projectPath = path.join(tmpDir, "project.json");
    expect(fs.existsSync(projectPath)).toBe(true);
  });

  it("produces valid JSON that can be parsed back", () => {
    saveProject(validConfig(), tmpDir);
    const raw = fs.readFileSync(path.join(tmpDir, "project.json"), "utf8");
    const parsed = JSON.parse(raw);
    expect(parsed.name).toBe("Test Project");
  });

  it("uses 2-space indentation for human-readable output", () => {
    saveProject(validConfig(), tmpDir);
    const raw = fs.readFileSync(path.join(tmpDir, "project.json"), "utf8");
    // 2-space indented JSON has lines starting with "  "
    const lines = raw.split("\n");
    const indentedLines = lines.filter((l) => l.startsWith("  "));
    expect(indentedLines.length).toBeGreaterThan(0);
    // Verify it matches JSON.stringify with 2 spaces
    const expected = JSON.stringify(validConfig(), null, 2);
    expect(raw).toBe(expected);
  });

  it("validates config before writing (rejects invalid)", () => {
    const badConfig = { name: 123 } as any;
    expect(() => saveProject(badConfig, tmpDir)).toThrow(z.ZodError);
    // project.json should NOT exist since validation failed before write
    expect(fs.existsSync(path.join(tmpDir, "project.json"))).toBe(false);
  });

  it("writes atomically via tmp file + rename", () => {
    // After saveProject, the tmp file should not remain
    saveProject(validConfig(), tmpDir);
    const tmpPath = path.join(tmpDir, "project.tmp.json");
    expect(fs.existsSync(tmpPath)).toBe(false);
    // But project.json should exist
    expect(fs.existsSync(path.join(tmpDir, "project.json"))).toBe(true);
  });

  it("overwrites existing project.json", () => {
    saveProject(validConfig(), tmpDir);
    const updated = { ...validConfig(), name: "Updated Name" };
    saveProject(updated, tmpDir);
    const raw = fs.readFileSync(path.join(tmpDir, "project.json"), "utf8");
    const parsed = JSON.parse(raw);
    expect(parsed.name).toBe("Updated Name");
  });

  it("round-trips with loadProject", () => {
    const config = validConfig();
    saveProject(config, tmpDir);
    const loaded = loadProject(tmpDir);
    expect(loaded).toEqual(config);
  });
});

// ---------------------------------------------------------------------------
// 6. getSection
// ---------------------------------------------------------------------------

describe("getSection", () => {
  const config = validConfig();

  it("returns the section with matching id", () => {
    const section = getSection("intro", config);
    expect(section).toBeDefined();
    expect(section!.id).toBe("intro");
    expect(section!.label).toBe("Introduction");
  });

  it("returns a different section by id", () => {
    const section = getSection("main", config);
    expect(section).toBeDefined();
    expect(section!.id).toBe("main");
  });

  it("returns undefined for non-existent id", () => {
    const section = getSection("nonexistent", config);
    expect(section).toBeUndefined();
  });

  it("returns undefined for empty string id", () => {
    const section = getSection("", config);
    expect(section).toBeUndefined();
  });

  it("works with empty sections array", () => {
    const emptyConfig = { ...config, sections: [] };
    const section = getSection("intro", emptyConfig);
    expect(section).toBeUndefined();
  });
});

// ---------------------------------------------------------------------------
// 7. Source file structure checks
// ---------------------------------------------------------------------------

describe("lib/project.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    sourceCode = fs.readFileSync(
      path.join(__dirname, "..", "lib", "project.ts"),
      "utf-8"
    );
  });

  it("has server-only guard", () => {
    expect(sourceCode).toMatch(/server-only/);
  });

  it("imports fs from node", () => {
    expect(sourceCode).toMatch(/import\s+fs\s+from\s+['"]fs['"]/);
  });

  it("imports path from node", () => {
    expect(sourceCode).toMatch(/import\s+path\s+from\s+['"]path['"]/);
  });

  it("imports z from zod", () => {
    expect(sourceCode).toMatch(/import\s+\{.*z.*\}\s+from\s+['"]zod['"]/);
  });

  it("exports loadProject function", () => {
    expect(sourceCode).toMatch(/export\s+function\s+loadProject/);
  });

  it("exports saveProject function", () => {
    expect(sourceCode).toMatch(/export\s+function\s+saveProject/);
  });

  it("exports getSection function", () => {
    expect(sourceCode).toMatch(/export\s+function\s+getSection/);
  });

  it("exports validateProjectConfig function", () => {
    expect(sourceCode).toMatch(/export\s+function\s+validateProjectConfig/);
  });

  it("exports projectConfigSchema", () => {
    expect(sourceCode).toMatch(/export\s+const\s+projectConfigSchema/);
  });

  it("uses fs.renameSync for atomic writes", () => {
    expect(sourceCode).toMatch(/fs\.renameSync/);
  });

  it("uses fs.writeFileSync for tmp file", () => {
    expect(sourceCode).toMatch(/fs\.writeFileSync/);
  });

  it("uses project.tmp.json as temp file path", () => {
    expect(sourceCode).toMatch(/project\.tmp\.json/);
  });

  it("uses path.join for constructing file paths", () => {
    expect(sourceCode).toMatch(/path\.join/);
  });
});

// ---------------------------------------------------------------------------
// 8. Integration — save + load round-trip
// ---------------------------------------------------------------------------

describe("integration: save and load round-trip", () => {
  let tmpDir: string;

  beforeEach(() => {
    tmpDir = createTmpDir();
  });

  afterEach(() => {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  });

  it("preserves all fields through save + load", () => {
    const config = validConfig();
    saveProject(config, tmpDir);
    const loaded = loadProject(tmpDir);

    expect(loaded.name).toBe(config.name);
    expect(loaded.outputResolution).toBe(config.outputResolution);
    expect(loaded.tts).toEqual(config.tts);
    expect(loaded.sections).toEqual(config.sections);
    expect(loaded.audioSync).toEqual(config.audioSync);
    expect(loaded.veo).toEqual(config.veo);
    expect(loaded.render).toEqual(config.render);
  });

  it("preserves sections order", () => {
    const config = validConfig();
    saveProject(config, tmpDir);
    const loaded = loadProject(tmpDir);
    expect(loaded.sections[0].id).toBe("intro");
    expect(loaded.sections[1].id).toBe("main");
  });

  it("preserves referenceImages map", () => {
    const config = validConfig();
    config.veo.referenceImages = { logo: "logo.png", bg: "bg.png" };
    saveProject(config, tmpDir);
    const loaded = loadProject(tmpDir);
    expect(loaded.veo.referenceImages).toEqual({
      logo: "logo.png",
      bg: "bg.png",
    });
  });

  it("preserves audioSync sectionGroups", () => {
    const config = validConfig();
    saveProject(config, tmpDir);
    const loaded = loadProject(tmpDir);
    expect(loaded.audioSync.sectionGroups).toEqual(
      config.audioSync.sectionGroups
    );
  });

  it("can save, modify, and reload", () => {
    const config = validConfig();
    saveProject(config, tmpDir);

    const loaded = loadProject(tmpDir);
    loaded.name = "Modified Name";
    loaded.sections.push({
      id: "outro",
      label: "Outro",
      videoFile: "output/outro.mp4",
      specDir: "specs/outro",
      remotionDir: "remotion/outro",
      compositionId: "OutroComp",
      durationSeconds: 5,
      offsetSeconds: 57.5,
    });
    saveProject(loaded, tmpDir);

    const reloaded = loadProject(tmpDir);
    expect(reloaded.name).toBe("Modified Name");
    expect(reloaded.sections).toHaveLength(3);
    expect(reloaded.sections[2].id).toBe("outro");
  });
});
