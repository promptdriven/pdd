import { NextRequest, NextResponse } from "next/server";
import {
  createProjectWorkspace,
  setSelectedProjectId,
} from "@/lib/projects";
import type { ProjectConfig } from "@/lib/types";

export const dynamic = "force-dynamic";

const normalizeProjectId = (value: string): string =>
  value
    .trim()
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "-")
    .replace(/^-+|-+$/g, "")
    .replace(/-{2,}/g, "-");

const buildDefaultProjectConfig = (name: string): ProjectConfig => ({
  name,
  outputResolution: { width: 1920, height: 1080 },
  tts: {
    engine: "qwen3-tts",
    modelPath: "models/Qwen3-TTS-12Hz-1.7B-CustomVoice",
    tokenizerPath: "models/Qwen3-TTS-Tokenizer-12Hz",
    speaker: "Aiden",
    speakingRate: 0.95,
    sampleRate: 24000,
  },
  sections: [],
  audioSync: { sectionGroups: {}, silenceGapDefault: 0.3 },
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
});

const buildStarterScript = (name: string): string => `# ${name} Script

Write your video script here.

Suggested format:
- Use \`## SECTION NAME\` headings for each video section
- Use \`**[VISUAL: ...]**\` lines for visual beats
- Use \`**NARRATOR:**\` before spoken lines
`;

export async function POST(request: NextRequest): Promise<NextResponse> {
  let body: { name?: string; projectId?: string } | null = null;

  try {
    body = (await request.json()) as { name?: string; projectId?: string };
  } catch {
    return NextResponse.json({ error: "Invalid JSON" }, { status: 400 });
  }

  const name = body?.name?.trim() ?? "";
  if (!name) {
    return NextResponse.json({ error: "Missing project name" }, { status: 400 });
  }

  const projectId = normalizeProjectId(body?.projectId?.trim() || name);
  if (!projectId) {
    return NextResponse.json({ error: "Invalid project id" }, { status: 400 });
  }

  try {
    createProjectWorkspace({
      projectId,
      config: buildDefaultProjectConfig(name),
      mainScriptContent: buildStarterScript(name),
    });
    setSelectedProjectId(projectId);

    return NextResponse.json(
      {
        ok: true,
        project: {
          id: projectId,
          name,
        },
      },
      { status: 200 },
    );
  } catch (error) {
    const message = error instanceof Error ? error.message : "Failed to create project";
    const status = /already exists/i.test(message) ? 409 : 500;
    return NextResponse.json({ error: message }, { status });
  }
}
