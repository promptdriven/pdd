import { NextResponse } from "next/server";
import { spawnSync } from "child_process";
import fs from "fs";
import path from "path";

import { parseSegmentsFromScript, getWavDuration } from "@/lib/tts-segments";
import { getAppScriptsDir, getProjectDir } from "@/lib/projects";

/**
 * Local TtsSegment type (required).
 */
interface TtsSegment {
  id: string;
  status: "done" | "missing" | "error";
  duration?: number;
  text?: string;
}

function ensureSegmentsManifest(outputDir: string): void {
  const manifestPath = path.join(outputDir, "segments.json");
  if (fs.existsSync(manifestPath)) {
    return;
  }

  const renderScriptPath = path.join(getAppScriptsDir(), "render_tts.py");
  if (!fs.existsSync(renderScriptPath)) {
    return;
  }

  const result = spawnSync(
    "python3",
    [
      renderScriptPath,
      "--project-dir",
      getProjectDir(),
      "--output-dir",
      "outputs/tts/",
      "--manifest-only",
    ],
    {
      cwd: getProjectDir(),
      env: {
        ...process.env,
        RENDER_TTS_ALLOW_EDGE_FALLBACK:
          process.env.RENDER_TTS_ALLOW_EDGE_FALLBACK ?? "1",
      },
      stdio: "pipe",
      encoding: "utf-8",
    },
  );

  if (result.status !== 0 && !fs.existsSync(manifestPath)) {
    console.warn(
      "Failed to build TTS segments manifest:",
      result.stderr || result.stdout,
    );
  }
}

/**
 * GET /api/pipeline/tts-render/segments
 * Returns TTS segments + status.
 */
export async function GET(): Promise<NextResponse> {
  const outputDir = path.join(getProjectDir(), "outputs", "tts");
  ensureSegmentsManifest(outputDir);
  const scriptSegments = parseSegmentsFromScript();

  const wavFiles = fs.existsSync(outputDir)
    ? fs.readdirSync(outputDir).filter((f) => f.endsWith(".wav"))
    : [];

  const wavSet = new Set(wavFiles.map((f) => f.replace(/\.wav$/, "")));

  const segments: TtsSegment[] = [];

  // From script
  for (const seg of scriptSegments) {
    const filePath = path.join(outputDir, `${seg.id}.wav`);
    const exists = wavSet.has(seg.id);
    if (exists) wavSet.delete(seg.id);

    segments.push({
      id: seg.id,
      status: exists ? "done" : "missing",
      duration: exists ? getWavDuration(filePath) : undefined,
      text: seg.text,
    });
  }

  // Extra WAVs not in script
  for (const id of wavSet) {
    const filePath = path.join(outputDir, `${id}.wav`);
    segments.push({
      id,
      status: "done",
      duration: getWavDuration(filePath),
    });
  }

  return NextResponse.json({ segments });
}
