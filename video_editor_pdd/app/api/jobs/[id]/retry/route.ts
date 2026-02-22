import { NextResponse } from "next/server";
import { getJob, retryJob } from "@/lib/jobs";

export const dynamic = "force-dynamic";

/**
 * POST /api/jobs/[id]/retry
 * Retries a failed job.
 */
export async function POST(
  _request: Request,
  { params }: { params: { id: string } }
): Promise<NextResponse> {
  try {
    const job = getJob(params.id);

    if (!job) {
      return NextResponse.json({ error: "Job not found" }, { status: 404 });
    }

    if (job.status !== "error") {
      return NextResponse.json(
        { error: "Job is not in error state" },
        { status: 400 }
      );
    }

    await retryJob(params.id);

    return NextResponse.json({ jobId: params.id }, { status: 200 });
  } catch (error) {
    console.error("Error retrying job:", error);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}