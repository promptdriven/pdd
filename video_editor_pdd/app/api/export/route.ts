import { NextResponse } from "next/server";
import { getDb } from "@/lib/db";

export const dynamic = "force-dynamic";

export async function GET(): Promise<NextResponse> {
  try {
    const db = getDb();
    const rows = db.prepare('SELECT * FROM annotations ORDER BY createdAt ASC').all() as Record<string, any>[];

    const annotations = rows.map((row) => ({
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
    }));

    const exportData = {
      exportedAt: new Date().toISOString(),
      count: annotations.length,
      annotations,
    };

    return new NextResponse(JSON.stringify(exportData, null, 2), {
      status: 200,
      headers: {
        'Content-Type': 'application/json',
        'Content-Disposition': 'attachment; filename="annotations-export.json"',
      },
    });
  } catch (error) {
    console.error("Error exporting annotations:", error);
    return NextResponse.json({ error: "Internal Server Error" }, { status: 500 });
  }
}
