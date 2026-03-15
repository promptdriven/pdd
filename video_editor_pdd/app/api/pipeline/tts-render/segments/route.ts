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
  const scriptPath = path.join(getProjectDir(), "narrative", "tts_script.md");
  const manifestExists = fs.existsSync(manifestPath);
  const scriptExists = fs.existsSync(scriptPath);

  let shouldRefresh = !manifestExists;
  if (!shouldRefresh && manifestExists && scriptExists) {
    try {
      shouldRefresh = fs.statSync(scriptPath).mtimeMs > fs.statSync(manifestPath).mtimeMs;
    } catch {
      shouldRefresh = false;
    }
  }

  if (!shouldRefresh) {
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

    segments.push({
      id: seg.id,
      status: exists ? "done" : "missing",
      duration: exists ? getWavDuration(filePath) : undefined,
      text: seg.text,
    });
  }

  return NextResponse.json({ segments });
}
