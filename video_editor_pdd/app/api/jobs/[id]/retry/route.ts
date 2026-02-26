import { NextResponse } from "next/server";
import { getJob, retryJob } from "@/lib/jobs";

export const dynamic = "force-dynamic";

/**
 * POST /api/jobs/[id]/retry
 * Retries a failed job by creating a new job linked via retryOf.
 */
export async function POST(
  _request: Request,
  { params }: { params: Promise<{ id: string }> }
): Promise<NextResponse> {
  try {
    const { id } = await params;
    const job = getJob(id);

    if (!job) {
      return NextResponse.json({ error: "Job not found" }, { status: 404 });
    }

    if (job.status !== "error") {
      return NextResponse.json(
        { error: "Job is not in error state" },
        { status: 409 }
      );
    }

    const newJobId = await retryJob(id);

    return NextResponse.json({ jobId: newJobId }, { status: 200 });
  } catch (error) {
    console.error("Error retrying job:", error);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}
