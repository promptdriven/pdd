import { NextRequest, NextResponse } from "next/server";
import { randomUUID } from "crypto";
import { parseAnnotationAnalysis } from "@/lib/annotation-analysis";
import { getDb } from "@/lib/db";
import { loadProject } from "@/lib/project";
import { resolveAnnotationTarget } from "@/lib/annotation-target";
import type { Annotation, CreateAnnotationInput } from "@/lib/types";

/**
 * GET /api/annotations
 * Optionally filter by section via ?section=SECTION_ID
 */
export async function GET(request: NextRequest): Promise<NextResponse> {
  try {
    const db = getDb();
    const url = new URL(request.url);
    const sectionId = url.searchParams.get("section");

    let rows: Array<Record<string, any>>;
    if (sectionId) {
      rows = db
        .prepare(
          `SELECT * FROM annotations
           WHERE sectionId = ?
           ORDER BY timestamp ASC`
        )
        .all(sectionId) as Array<Record<string, any>>;
    } else {
      rows = db
        .prepare(`SELECT * FROM annotations ORDER BY timestamp ASC`)
        .all() as Array<Record<string, any>>;
    }

    const annotations: Annotation[] = rows.map((row) => ({
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
      inputMethod: row.inputMethod ?? "typed",
      createdAt: row.createdAt,
    }));

    return NextResponse.json({ annotations }, { status: 200 });
  } catch (error) {
    console.error("Error fetching annotations:", error);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}

/**
 * POST /api/annotations
 * Create a new annotation.
 */
export async function POST(request: NextRequest): Promise<NextResponse> {
  try {
    const db = getDb();
    const body = (await request.json()) as CreateAnnotationInput;

    const {
      sectionId,
      timestamp,
      text,
      drawingDataUrl,
      compositeDataUrl,
      videoFile,
      inputMethod,
    } = body;

    if (!sectionId || (!drawingDataUrl && (text === undefined || text === "" || (typeof text === "string" && text.trim() === "")))) {
      return NextResponse.json(
        { error: "Missing required fields: sectionId is required, and either text (non-empty) or drawingDataUrl must be provided." },
        { status: 400 }
      );
    }

    const project = loadProject();
    const target = resolveAnnotationTarget(project, {
      sectionId,
      timestamp: timestamp ?? null,
      videoFile: videoFile ?? null,
    });

    const id = randomUUID();
    const createdAt = new Date().toISOString();

    db.prepare(
      `INSERT INTO annotations (
        id,
        sectionId,
        timestamp,
        text,
        videoFile,
        drawingDataUrl,
        compositeDataUrl,
        analysis,
        resolved,
        resolveJobId,
        createdAt,
        inputMethod
      ) VALUES (?, ?, ?, ?, ?, ?, ?, NULL, 0, NULL, ?, ?)`
    ).run(
      id,
      target.sectionId,
      target.timestamp,
      text,
      videoFile ?? null,
      drawingDataUrl ?? null,
      compositeDataUrl ?? null,
      createdAt,
      inputMethod ?? "typed"
    );

    const annotation: Annotation = {
      id,
      sectionId: target.sectionId,
      timestamp: target.timestamp,
      text,
      videoFile: videoFile ?? null,
      drawingDataUrl: drawingDataUrl ?? null,
      compositeDataUrl: compositeDataUrl ?? null,
      analysis: null,
      resolved: false,
      resolveJobId: null,
      inputMethod: inputMethod ?? "typed",
      createdAt,
    };

    return NextResponse.json(annotation, { status: 201 });
  } catch (error) {
    console.error("Error creating annotation:", error);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}
