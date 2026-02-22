import { NextResponse } from "next/server";
import fs from "fs";
import path from "path";

import { parseSegmentsFromScript, getWavDuration } from "../run/route";

/**
 * Local TtsSegment type (required).
 */
interface TtsSegment {
  id: string;
  status: "done" | "missing" | "error";
  duration?: number;
  text?: string;
}

/**
 * GET /api/pipeline/tts-render/segments
 * Returns TTS segments + status.
 */
export async function GET(): Promise<NextResponse> {
  const outputDir = path.join(process.cwd(), "outputs", "tts");
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
