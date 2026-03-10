import { NextResponse } from "next/server";
import fs from "fs";
import os from "os";
import path from "path";

import { parseAnnotationAnalysis } from "@/lib/annotation-analysis";
import { getDb } from "@/lib/db";
import { runClaudeAnalysis } from "@/lib/claude";
import { loadProject } from "@/lib/project";
import { resolveAnnotationTarget } from "@/lib/annotation-target";
import type { Annotation, AnnotationAnalysis } from "@/lib/types";

export const dynamic = "force-dynamic";

function mapAnnotationRow(row: any): Annotation {
  return {
    id: row.id,
    sectionId: row.sectionId,
    timestamp: row.timestamp,
    text: row.text,
    videoFile: row.videoFile ?? null,
    drawingDataUrl: row.drawingDataUrl ?? null,
    compositeDataUrl: row.compositeDataUrl ?? null,
    analysis: parseAnnotationAnalysis(row.analysis),
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
  const project = loadProject();
  const target = resolveAnnotationTarget(project, {
    sectionId: annotation.sectionId,
    timestamp: annotation.timestamp,
    videoFile: annotation.videoFile,
  });
  const normalizedAnnotation = target.normalized
    ? {
        ...annotation,
        sectionId: target.sectionId,
        timestamp: target.timestamp,
      }
    : annotation;

  if (target.normalized) {
    db.prepare("UPDATE annotations SET sectionId = ?, timestamp = ? WHERE id = ?").run(
      target.sectionId,
      target.timestamp,
      id
    );
  }

  let tmpPath: string | null = null;
  let overlayTmpPath: string | null = null;

  try {
    if (!normalizedAnnotation.compositeDataUrl) {
      throw new Error("Annotation has no compositeDataUrl");
    }

    // Write composite image to temp file
    tmpPath = path.join(
      os.tmpdir(),
      `annotation_${id}_composite.png`
    );
    fs.writeFileSync(
      tmpPath,
      Buffer.from(normalizedAnnotation.compositeDataUrl.split(",")[1], "base64")
    );

    if (normalizedAnnotation.drawingDataUrl) {
      overlayTmpPath = path.join(os.tmpdir(), `annotation_${id}_overlay.png`);
      fs.writeFileSync(
        overlayTmpPath,
        Buffer.from(normalizedAnnotation.drawingDataUrl.split(",")[1], "base64")
      );
    }

    // Build prompt for Claude
    const prompt = `
Analyze this annotation for section ${normalizedAnnotation.sectionId}. Annotation text: ${normalizedAnnotation.text}. Review the spec files in specs/${normalizedAnnotation.sectionId}/ and the provided image files.

Composite frame PNG: ${tmpPath}
${overlayTmpPath ? `Overlay markup PNG: ${overlayTmpPath}` : "Overlay markup PNG: none"}

If an overlay markup PNG is present, treat the orange markup as the user's exact target region.
- An orange circle means "this object/area"
- An arrow means "this point/element"
- Freehand markup indicates the exact area under discussion
Prioritize the marked region over the rest of the scene when deciding what "this" refers to.

Return JSON only matching AnnotationAnalysis:
{
  "severity": "critical" | "major" | "minor" | "pass",
  "fixType": "remotion" | "veo" | "tts" | "none",
  "technicalAssessment": string,
  "suggestedFixes": string[],
  "confidence": number
}

Do not return markdown, prose outside the JSON object, or a Claude result envelope.
Do not ignore the markup overlay when one is provided.
`.trim();

    const rawAnalysis = await runClaudeAnalysis(prompt, (line) => {
      console.log(`[Claude] ${line}`);
    });
    const analysis = parseAnnotationAnalysis(rawAnalysis);

    if (!analysis) {
      throw new Error("Claude returned invalid AnnotationAnalysis payload");
    }

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
    if (overlayTmpPath && fs.existsSync(overlayTmpPath)) {
      try {
        fs.unlinkSync(overlayTmpPath);
      } catch (err) {
        console.warn("Failed to delete temp file:", err);
      }
    }
  }
}
