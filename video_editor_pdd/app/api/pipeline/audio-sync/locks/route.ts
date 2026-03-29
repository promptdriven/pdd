import path from "path";
import { NextRequest, NextResponse } from "next/server";
import { getProjectDir } from "@/lib/projects";
import {
  computeFileSha256,
  loadAudioSyncValidationLocks,
  saveAudioSyncValidationLocks,
} from "../_lib/validation-locks";

interface LockRequestBody {
  sectionId?: string;
  segmentId?: string;
}

function getSegmentAudioPath(projectDir: string, segmentId: string): string {
  return path.join(projectDir, "outputs", "tts", `${segmentId}.wav`);
}

export async function POST(request: NextRequest): Promise<NextResponse> {
  const body = (await request.json().catch(() => ({}))) as LockRequestBody;
  if (!body.sectionId || !body.segmentId) {
    return NextResponse.json(
      { error: "Missing sectionId or segmentId" },
      { status: 400 }
    );
  }

  const projectDir = getProjectDir();
  const segmentAudioPath = getSegmentAudioPath(projectDir, body.segmentId);

  try {
    const audioFingerprint = await computeFileSha256(segmentAudioPath);
    const locks = await loadAudioSyncValidationLocks(projectDir, body.sectionId);
    locks.segments[body.segmentId] = {
      segmentId: body.segmentId,
      audioFingerprint,
      acceptedAt: new Date().toISOString(),
    };
    await saveAudioSyncValidationLocks(projectDir, body.sectionId, locks);

    return NextResponse.json({
      ok: true,
      lock: locks.segments[body.segmentId],
    });
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === "ENOENT") {
      return NextResponse.json(
        { error: "Segment audio not found" },
        { status: 404 }
      );
    }

    console.error("Failed to save audio-sync lock:", error);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}

export async function DELETE(request: NextRequest): Promise<NextResponse> {
  const body = (await request.json().catch(() => ({}))) as LockRequestBody;
  if (!body.sectionId || !body.segmentId) {
    return NextResponse.json(
      { error: "Missing sectionId or segmentId" },
      { status: 400 }
    );
  }

  try {
    const projectDir = getProjectDir();
    const locks = await loadAudioSyncValidationLocks(projectDir, body.sectionId);
    delete locks.segments[body.segmentId];
    await saveAudioSyncValidationLocks(projectDir, body.sectionId, locks);
    return NextResponse.json({ ok: true });
  } catch (error) {
    console.error("Failed to remove audio-sync lock:", error);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}
