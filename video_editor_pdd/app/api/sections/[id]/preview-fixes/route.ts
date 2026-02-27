import { NextResponse } from "next/server";
import { getDb } from "@/lib/db";
import { runClaudeFixDryRun } from "@/lib/claude";
import type { Annotation, AnnotationAnalysis } from "@/lib/types";

export const dynamic = "force-dynamic";

type RouteParams = { params: Promise<{ id: string }> };

interface FixPreview {
  annotationId: string;
  fixType: string;
  preview: string;
  diff: string | null;
  filesModified: string[];
  confidence: number;
}

function buildPreviewPrompt(annotation: Annotation): string {
  const analysisJson = annotation.analysis ? JSON.stringify(annotation.analysis, null, 2) : "none";
  return `
You are previewing a Remotion fix for a visual issue in the "${annotation.sectionId}" section.

Issue details:
- Annotation ID: ${annotation.id}
- Timestamp: ${annotation.timestamp}s
- User note: ${annotation.text}
- Analysis: ${analysisJson}

Instructions:
1. Use Glob/Read tools to inspect the relevant TSX source files in this directory (remotion/src/remotion/).
2. Identify which file(s) need to change to resolve the issue.
3. Do NOT modify any files — this is a preview/dry-run only.
4. Return JSON describing what you would change:
{
  "fixType": "remotion",
  "filesModified": ["list of files you would modify"],
  "changeDescription": "detailed description of what you would change and why",
  "confidence": 0.0-1.0,
  "proposedDiff": "unified diff format showing the proposed changes"
}
`.trim();
}

export async function POST(request: Request, { params }: RouteParams) {
  const { id: sectionId } = await params;
  const db = getDb();

  try {
    // Check for optional annotationIds filter in request body
    let annotationIds: string[] | null = null;
    try {
      const body = await request.json();
      if (body.annotationIds && Array.isArray(body.annotationIds)) {
        annotationIds = body.annotationIds;
      }
    } catch {
      // No body or invalid JSON — process all unresolved
    }

    // Load unresolved annotations for the section
    let rows: Array<Record<string, unknown>>;
    if (annotationIds && annotationIds.length > 0) {
      const placeholders = annotationIds.map(() => '?').join(',');
      rows = db
        .prepare(
          `SELECT * FROM annotations WHERE sectionId = ? AND id IN (${placeholders}) AND resolved = 0 ORDER BY timestamp ASC`
        )
        .all(sectionId, ...annotationIds) as Array<Record<string, unknown>>;
    } else {
      rows = db
        .prepare(
          `SELECT * FROM annotations WHERE sectionId = ? AND resolved = 0 ORDER BY timestamp ASC`
        )
        .all(sectionId) as Array<Record<string, unknown>>;
    }

    if (!rows || rows.length === 0) {
      return NextResponse.json({ previews: [], message: "No unresolved annotations" });
    }

    // Deserialize annotations
    const annotations: Annotation[] = rows.map((row) => {
      const analysisRaw = row.analysis as string | null;
      const analysis: AnnotationAnalysis | null = analysisRaw ? JSON.parse(analysisRaw) : null;
      return {
        id: String(row.id),
        sectionId: String(row.sectionId),
        timestamp: Number(row.timestamp),
        text: String(row.text ?? ""),
        videoFile: (row.videoFile as string | null) ?? null,
        drawingDataUrl: (row.drawingDataUrl as string | null) ?? null,
        compositeDataUrl: (row.compositeDataUrl as string | null) ?? null,
        analysis,
        resolved: Boolean(row.resolved),
        resolveJobId: (row.resolveJobId as string | null) ?? null,
        createdAt: String(row.createdAt ?? ""),
      };
    });

    // Group by fix type
    const byFixType: Record<string, Annotation[]> = {
      remotion: [],
      veo: [],
      tts: [],
      manual: [],
      none: [],
    };

    for (const ann of annotations) {
      const fixType = ann.analysis?.fixType ?? "manual";
      if (byFixType[fixType]) byFixType[fixType].push(ann);
    }

    // Generate previews
    const previews: FixPreview[] = [];

    // Remotion fixes: run Claude in dry-run mode
    for (const ann of byFixType.remotion) {
      try {
        const result = await runClaudeFixDryRun(
          buildPreviewPrompt(ann),
          "remotion/src/remotion/"
        );
        previews.push({
          annotationId: ann.id,
          fixType: "remotion",
          preview: result.changeDescription,
          diff: result.proposedDiff || null,
          filesModified: result.filesModified,
          confidence: result.confidence,
        });
      } catch (err) {
        previews.push({
          annotationId: ann.id,
          fixType: "remotion",
          preview: `Preview failed: ${err instanceof Error ? err.message : 'Unknown error'}`,
          diff: null,
          filesModified: [],
          confidence: 0,
        });
      }
    }

    // Veo fixes: placeholder preview
    for (const ann of byFixType.veo) {
      previews.push({
        annotationId: ann.id,
        fixType: "veo",
        preview: "Veo clip will be regenerated with updated prompt",
        diff: null,
        filesModified: [],
        confidence: ann.analysis?.confidence ?? 0,
      });
    }

    // TTS fixes: placeholder preview
    for (const ann of byFixType.tts) {
      previews.push({
        annotationId: ann.id,
        fixType: "tts",
        preview: "TTS segment will be re-rendered with updated parameters",
        diff: null,
        filesModified: [],
        confidence: ann.analysis?.confidence ?? 0,
      });
    }

    return NextResponse.json({ previews });
  } catch (error) {
    console.error("Preview fixes failed:", error);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}
