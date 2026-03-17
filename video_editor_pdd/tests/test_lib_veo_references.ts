import fs from "fs";
import os from "os";
import path from "path";

import {
  collectInferredVeoReferences,
  mergeInferredVeoReferences,
  syncInferredVeoReferencesFromProjectSpecs,
} from "../lib/veo-references";
import type { ProjectConfig, VeoReference } from "../lib/types";

function createTmpDir(): string {
  return fs.mkdtempSync(path.join(os.tmpdir(), "pdd-veo-ref-test-"));
}

function makeConfig(): ProjectConfig {
  return {
    name: "Test Project",
    outputResolution: { width: 1920, height: 1080 },
    tts: {
      engine: "qwen3-tts",
      modelPath: "model",
      tokenizerPath: "tokenizer",
      speaker: "Aiden",
      speakingRate: 1,
      sampleRate: 24000,
    },
    sections: [
      {
        id: "cold_open",
        label: "Cold Open",
        videoFile: "output/sections/cold_open.mp4",
        specDir: "cold_open",
        remotionDir: "remotion/cold_open",
        compositionId: "ColdOpen",
        durationSeconds: 5,
        offsetSeconds: 0,
      },
      {
        id: "closing",
        label: "Closing",
        videoFile: "output/sections/closing.mp4",
        specDir: "closing",
        remotionDir: "remotion/closing",
        compositionId: "Closing",
        durationSeconds: 5,
        offsetSeconds: 5,
      },
    ],
    audioSync: {
      sectionGroups: {},
      silenceGapDefault: 0.3,
    },
    veo: {
      model: "veo-3.1-generate-preview",
      defaultAspectRatio: "16:9",
      maxConcurrentGenerations: 4,
      references: [],
      frameChains: [],
    },
    render: {
      maxParallelRenders: 3,
      useLambda: false,
      lambdaRegion: "us-east-1",
    },
  };
}

describe("collectInferredVeoReferences", () => {
  it("deduplicates recurring characters across sections and unions their sections", () => {
    const references = collectInferredVeoReferences([
      {
        sectionId: "cold_open",
        path: "specs/cold_open/01_grandmother_intro.md",
        content: [
          "[veo:]",
          "",
          "## Data Points",
          "```json",
          "{",
          '  "type": "veo_clip",',
          '  "clipId": "grandmother_intro",',
          '  "characters": [',
          '    { "id": "grandmother", "label": "Grandmother", "referencePrompt": "Warm portrait of the grandmother under a lamp." }',
          "  ]",
          "}",
          "```",
        ].join("\n"),
      },
      {
        sectionId: "closing",
        path: "specs/closing/02_grandmother_callback.md",
        content: [
          "[veo:]",
          "",
          "## Data Points",
          "```json",
          "{",
          '  "type": "veo_clip",',
          '  "clipId": "grandmother_callback",',
          '  "characters": [',
          '    { "id": "grandmother", "label": "Grandmother", "referencePrompt": "Warm portrait of the grandmother under a lamp." }',
          "  ]",
          "}",
          "```",
        ].join("\n"),
      },
    ]);

    expect(references).toEqual([
      expect.objectContaining({
        id: "grandmother",
        label: "Grandmother",
        imagePath: "outputs/veo/references/grandmother.png",
        sections: ["closing", "cold_open"],
        referencePrompt: "Warm portrait of the grandmother under a lamp.",
        source: "stage6-inferred",
      }),
    ]);
  });
});

describe("mergeInferredVeoReferences", () => {
  it("preserves manual references while keeping inferred section coverage", () => {
    const manual: VeoReference[] = [
      {
        id: "grandmother",
        label: "Grandma Nora",
        imagePath: "custom/grandma-nora.png",
        sections: ["manual_section"],
        source: "manual",
        referencePrompt: "Custom portrait prompt",
      },
    ];
    const inferred: VeoReference[] = [
      {
        id: "grandmother",
        label: "Grandmother",
        imagePath: "outputs/veo/references/grandmother.png",
        sections: ["closing", "cold_open"],
        source: "stage6-inferred",
        referencePrompt: "Warm portrait of the grandmother under a lamp.",
      },
    ];

    expect(mergeInferredVeoReferences(manual, inferred)).toEqual([
      expect.objectContaining({
        id: "grandmother",
        label: "Grandma Nora",
        imagePath: "custom/grandma-nora.png",
        sections: ["closing", "cold_open", "manual_section"],
        source: "manual",
        referencePrompt: "Custom portrait prompt",
      }),
    ]);
  });
});

describe("syncInferredVeoReferencesFromProjectSpecs", () => {
  it("scans project specs and writes inferred stage6 references into the returned config", () => {
    const dir = createTmpDir();
    const config = makeConfig();
    fs.mkdirSync(path.join(dir, "specs", "cold_open"), { recursive: true });
    fs.mkdirSync(path.join(dir, "specs", "closing"), { recursive: true });

    fs.writeFileSync(
      path.join(dir, "specs", "cold_open", "01_grandmother_intro.md"),
      [
        "[veo:]",
        "",
        "## Data Points",
        "```json",
        "{",
        '  "type": "veo_clip",',
        '  "clipId": "grandmother_intro",',
        '  "characters": [',
        '    { "id": "grandmother", "label": "Grandmother", "referencePrompt": "Portrait of the same grandmother under a warm lamp." }',
        "  ]",
        "}",
        "```",
      ].join("\n")
    );
    fs.writeFileSync(
      path.join(dir, "specs", "closing", "02_grandmother_callback.md"),
      [
        "[veo:]",
        "",
        "## Data Points",
        "```json",
        "{",
        '  "type": "veo_clip",',
        '  "clipId": "grandmother_callback",',
        '  "characters": [',
        '    { "id": "grandmother", "label": "Grandmother", "referencePrompt": "Portrait of the same grandmother under a warm lamp." }',
        "  ]",
        "}",
        "```",
      ].join("\n")
    );

    const synced = syncInferredVeoReferencesFromProjectSpecs(dir, config);

    expect(synced.veo.references).toEqual([
      expect.objectContaining({
        id: "grandmother",
        sections: ["closing", "cold_open"],
        imagePath: "outputs/veo/references/grandmother.png",
        referencePrompt: "Portrait of the same grandmother under a warm lamp.",
        source: "stage6-inferred",
      }),
    ]);
  });

  it("accepts inferred characters from specs that use a 'Data Points JSON' heading", () => {
    const dir = createTmpDir();
    const config = makeConfig();
    fs.mkdirSync(path.join(dir, "specs", "cold_open"), { recursive: true });
    fs.mkdirSync(path.join(dir, "specs", "closing"), { recursive: true });

    fs.writeFileSync(
      path.join(dir, "specs", "cold_open", "01_developer_intro.md"),
      [
        "[veo:]",
        "",
        "## Data Points JSON",
        "```json",
        "{",
        '  "type": "veo_clip",',
        '  "clipId": "developer_intro",',
        '  "characters": [',
        '    { "id": "developer_protagonist", "label": "Developer", "referencePrompt": "Modern software developer in front of a dark-themed editor." }',
        "  ]",
        "}",
        "```",
      ].join("\n")
    );
    fs.writeFileSync(
      path.join(dir, "specs", "closing", "02_developer_callback.md"),
      [
        "[veo:]",
        "",
        "## Data Points JSON",
        "```json",
        "{",
        '  "type": "veo_clip",',
        '  "clipId": "developer_callback",',
        '  "characters": [',
        '    { "id": "developer_protagonist", "label": "Developer", "referencePrompt": "Modern software developer in front of a dark-themed editor." }',
        "  ]",
        "}",
        "```",
      ].join("\n")
    );

    const synced = syncInferredVeoReferencesFromProjectSpecs(dir, config);

    expect(synced.veo.references).toEqual([
      expect.objectContaining({
        id: "developer_protagonist",
        label: "Developer",
        sections: ["closing", "cold_open"],
        imagePath: "outputs/veo/references/developer_protagonist.png",
        referencePrompt:
          "Modern software developer in front of a dark-themed editor.",
        source: "stage6-inferred",
      }),
    ]);
  });
});
