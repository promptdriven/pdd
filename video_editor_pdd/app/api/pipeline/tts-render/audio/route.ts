import fs from "fs";
import path from "path";
import { NextResponse } from "next/server";

import { getProjectDir } from "@/lib/projects";

interface RestoreSegmentPayload {
  segmentId: string;
  audioBase64: string;
}

function isValidRestoreSegmentPayload(
  value: unknown,
): value is RestoreSegmentPayload {
  if (!value || typeof value !== "object") {
    return false;
  }

  const segmentId = (value as RestoreSegmentPayload).segmentId;
  const audioBase64 = (value as RestoreSegmentPayload).audioBase64;

  return (
    typeof segmentId === "string" &&
    /^[A-Za-z0-9][A-Za-z0-9_-]*$/.test(segmentId) &&
    typeof audioBase64 === "string" &&
    audioBase64.length > 0
  );
}

export async function POST(request: Request): Promise<Response> {
  const body = await request.json().catch(() => ({}));
  const segments = Array.isArray(body?.segments) ? body.segments : [];

  if (
    segments.length === 0 ||
    !segments.every((segment) => isValidRestoreSegmentPayload(segment))
  ) {
    return NextResponse.json(
      { error: "Invalid segment restore payload" },
      { status: 400 },
    );
  }

  const outputDir = path.join(getProjectDir(), "outputs", "tts");
  fs.mkdirSync(outputDir, { recursive: true });

  for (const { segmentId, audioBase64 } of segments as RestoreSegmentPayload[]) {
    const filePath = path.join(outputDir, `${segmentId}.wav`);
    fs.writeFileSync(filePath, Buffer.from(audioBase64, "base64"));
  }

  return NextResponse.json({ restoredCount: segments.length });
}
