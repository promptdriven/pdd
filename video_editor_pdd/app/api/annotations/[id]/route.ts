// app/api/annotations/[id]/route.ts
import { NextResponse } from "next/server";
import { getDb } from "@/lib/db";

export const dynamic = "force-dynamic";

/**
 * GET /api/annotations/[id]
 * Returns a single annotation by ID.
 */
export async function GET(
  request: Request,
  { params }: { params: { id: string } }
): Promise<NextResponse> {
  try {
    const db = getDb();
    const { id } = params;

    const row = db
      .prepare(`SELECT * FROM annotations WHERE id = ?`)
      .get(id) as Record<string, any> | undefined;

    if (!row) {
      return NextResponse.json(
        { error: "Annotation not found" },
        { status: 404 }
      );
    }

    // Build Annotation shape with parsed analysis JSON
    const annotation = {
      id: row.id,
      sectionId: row.sectionId,
      timestamp: row.timestamp,
      text: row.text,
      videoFile: row.videoFile ?? null,
      drawingDataUrl: row.drawingDataUrl ?? null,
      compositeDataUrl: row.compositeDataUrl ?? null,
      analysis: row.analysis ? JSON.parse(row.analysis) : null,
      resolved: Boolean(row.resolved),
      resolveJobId: row.resolveJobId ?? null,
      createdAt: row.createdAt,
    };

    return NextResponse.json(annotation);
  } catch (error) {
    console.error("Error fetching annotation:", error);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}