// app/api/jobs/[id]/route.ts
import { NextResponse } from "next/server";
import { getJob } from "@/lib/jobs";

export const dynamic = "force-dynamic";

/**
 * GET /api/jobs/[id]
 * Returns the current Job record for polling fallback.
 */
export async function GET(
  _request: Request,
  { params }: { params: { id: string } }
): Promise<NextResponse> {
  try {
    const job = getJob(params.id);

    if (!job) {
      return NextResponse.json({ error: "Job not found" }, { status: 404 });
    }

    return NextResponse.json(job);
  } catch (error) {
    console.error("Error fetching job:", error);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}