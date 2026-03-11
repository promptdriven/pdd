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

function isClaudeAuthFailure(error: unknown): boolean {
  const message = error instanceof Error ? error.message : String(error ?? "");
  return (
    message.includes("Failed to authenticate") ||
    message.includes("authentication_error") ||
    message.includes("Invalid authentication credentials") ||
    message.includes("API Error: 401")
  );
}

function inferFallbackFixType(text: string): AnnotationAnalysis["fixType"] {
  const normalized = text.toLowerCase();
  if (
    normalized.includes("audio") ||
    normalized.includes("voice") ||
    normalized.includes("narration") ||
    normalized.includes("tts")
  ) {
    return "tts";
  }
  if (
    normalized.includes("clip") ||
    normalized.includes("footage") ||
    normalized.includes("regenerate") ||
    normalized.includes("bird") ||
    normalized.includes("balloon") ||
    normalized.includes("couple") ||
    normalized.includes("sky")
  ) {
    return "veo";
  }
  return "remotion";
}

function buildFallbackAnalysis(annotation: Annotation): AnnotationAnalysis {
  const requestedChange = annotation.text.trim() || "Visual change requested";
  return {
    severity: "major",
    fixType: inferFallbackFixType(requestedChange),
    technicalAssessment: `Claude analysis was unavailable due to authentication; using fallback analysis based on the annotation text: ${requestedChange}`,
    suggestedFixes: [requestedChange],
    confidence: 0.25,
  };
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
    analysis: parseAnnotationAnalysis(row.analysis),
    resolved: Boolean(row.resolved),
    resolveJobId: row.resolveJobId ?? null,
    fixCommitSha: row.fixCommitSha ?? null,
    inputMethod: row.inputMethod ?? "typed",
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

Use fixType="remotion" for layout, compositing, timing, labeling, side-swaps, overlays, or other changes that can be made by editing the Remotion composition around existing footage.
Use fixType="veo" only when the underlying footage itself must be regenerated because the clip content is wrong.
When a Veo-backed scene is arranged inside a Remotion split-screen or overlay, prefer fixType="remotion" if the request is about placement or swapping existing footage.

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

    let analysis: AnnotationAnalysis | null = null;
    try {
      const rawAnalysis = await runClaudeAnalysis(prompt, (line) => {
        console.log(`[Claude] ${line}`);
      });
      analysis = parseAnnotationAnalysis(rawAnalysis);

      if (!analysis) {
        throw new Error("Claude returned invalid AnnotationAnalysis payload");
      }
    } catch (error) {
      if (!isClaudeAuthFailure(error)) {
        throw error;
      }
      console.warn("Claude analysis unavailable due to authentication; using fallback analysis");
      analysis = buildFallbackAnalysis(normalizedAnnotation);
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
