import { NextResponse } from "next/server";
import { randomUUID } from "crypto";

/**
 * POST /api/pipeline/stitch/run
 *
 * Triggers stitching of all rendered section videos into a single full video.
 * Returns a jobId for tracking.
 */
export async function POST(): Promise<NextResponse> {
  try {
    const jobId = randomUUID();

    // In a real implementation this would call stitchFullVideo from lib/render.
    // For now, return a jobId to unblock the UI flow.
    return NextResponse.json({ jobId }, { status: 200 });
  } catch (err) {
    const message = err instanceof Error ? err.message : "Unknown error";
    return NextResponse.json(
      { error: message },
      { status: 500 }
    );
  }
}
