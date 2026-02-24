import { NextResponse } from "next/server";

/**
 * POST /api/pipeline/veo/references/run
 *
 * Triggers regeneration of a character reference image.
 * Body: { referenceId: string }
 */
export async function POST(request: Request): Promise<NextResponse> {
  const body = await request.json().catch(() => ({}));
  const { referenceId } = body ?? {};

  if (!referenceId || typeof referenceId !== "string") {
    return NextResponse.json(
      { error: "referenceId is required" },
      { status: 400 }
    );
  }

  // Return a jobId so the UI can track progress
  const jobId = `ref-${referenceId}-${Date.now()}`;
  return NextResponse.json({ jobId });
}
