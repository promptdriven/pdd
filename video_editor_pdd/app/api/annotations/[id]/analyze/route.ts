import { NextResponse } from "next/server";
import fs from "fs";
import os from "os";
import path from "path";

import { getDb } from "@/lib/db";
import { runClaudeAnalysis } from "@/lib/claude";
import type { Annotation, AnnotationAnalysis } from "@/lib/types";

export const dynamic = "force-dynamic";

function parseAnalysis(value: unknown): AnnotationAnalysis | null {
  if (!value) return null;
  if (typeof value === "string") {
    try {
      return JSON.parse(value) as AnnotationAnalysis;
    } catch {
      return null;
    }
  }
  return value as AnnotationAnalysis;
}

function mapAnnotationRow(row: any): Annotation {
  return {
    id: row.id,
    sectionId: row.sectionId,
    timestamp: row.timestamp,
    text: row.text,
    videoFile: row.videoFile ?? null,
    drawingDataUrl: row.drawingDataUrl ?? null,
    compositeDataUrl: row.compositeDataUrl ?? null,
    analysis:
      parseAnalysis(row.analysis) ?? null,
    resolved: Boolean(row.resolved),
    resolveJobId: row.resolveJobId ?? null,
    createdAt: row.createdAt,
  };
}

export async function POST(
  request: Request,
  { params }: { params: Promise<{ id: string }> }
): Promise<NextResponse> {
  const { id } = await params;
  const db = getDb();

  // Load annotation
  const row = db
    .prepare("SELECT * FROM annotations WHERE id = ?")
    .get(id) as Record<string, unknown> | undefined;

  if (!row) {
    return NextResponse.json(
      { error: "Annotation not found" },
      { status: 404 }
    );
  }

  const annotation = mapAnnotationRow(row);

  let tmpPath: string | null = null;

  try {
    if (!annotation.compositeDataUrl) {
      throw new Error("Annotation has no compositeDataUrl");
    }

    // Write composite image to temp file
    tmpPath = path.join(
      os.tmpdir(),
      `annotation_${id}_composite.png`
    );
    fs.writeFileSync(
      tmpPath,
      Buffer.from(annotation.compositeDataUrl.split(",")[1], "base64")
    );

    // Build prompt for Claude
    const prompt = `Analyze this annotation for section ${annotation.sectionId}. Annotation text: ${annotation.text}. Review the spec files in specs/${annotation.sectionId}/ and the composite frame image provided.`;

    const analysis = await runClaudeAnalysis(prompt, (line) => {
      console.log(`[Claude] ${line}`);
    });

    // Store analysis JSON in DB
    db.prepare("UPDATE annotations SET analysis = ? WHERE id = ?").run(
      JSON.stringify(analysis),
      id
    );

    // Re-read updated annotation
    const updatedRow = db
      .prepare("SELECT * FROM annotations WHERE id = ?")
      .get(id) as Record<string, unknown>;

    const updatedAnnotation = mapAnnotationRow(updatedRow);

    return NextResponse.json(
      { annotation: updatedAnnotation },
      { status: 200 }
    );
  } catch (error) {
    console.error("Claude analysis failed:", error);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  } finally {
    if (tmpPath && fs.existsSync(tmpPath)) {
      try {
        fs.unlinkSync(tmpPath);
      } catch (err) {
        console.warn("Failed to delete temp file:", err);
      }
    }
  }
}