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
  { params }: { params: Promise<{ id: string }> }
): Promise<NextResponse> {
  try {
    const db = getDb();
    const { id } = await params;

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
      inputMethod: row.inputMethod ?? "typed",
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

/**
 * PUT /api/annotations/[id]
 * Updates an existing annotation.
 */
export async function PUT(
  request: Request,
  { params }: { params: Promise<{ id: string }> }
): Promise<NextResponse> {
  try {
    const db = getDb();
    const { id } = await params;

    const existing = db.prepare('SELECT id FROM annotations WHERE id = ?').get(id);
    if (!existing) {
      return NextResponse.json({ error: 'Annotation not found' }, { status: 404 });
    }

    const body = await request.json();
    const { text, sectionId, timestamp, analysis } = body;

    const updates: string[] = [];
    const values: unknown[] = [];

    if (text !== undefined) { updates.push('text = ?'); values.push(text); }
    if (sectionId !== undefined) { updates.push('sectionId = ?'); values.push(sectionId); }
    if (timestamp !== undefined) { updates.push('timestamp = ?'); values.push(timestamp); }
    if (analysis !== undefined) { updates.push('analysis = ?'); values.push(JSON.stringify(analysis)); }

    if (updates.length === 0) {
      return NextResponse.json({ error: 'No fields to update' }, { status: 400 });
    }

    values.push(id);
    db.prepare(`UPDATE annotations SET ${updates.join(', ')} WHERE id = ?`).run(...values);

    // Re-fetch and return updated annotation
    const row = db.prepare('SELECT * FROM annotations WHERE id = ?').get(id) as Record<string, any>;
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
      inputMethod: row.inputMethod ?? "typed",
      createdAt: row.createdAt,
    };

    return NextResponse.json(annotation);
  } catch (error) {
    console.error('Error updating annotation:', error);
    return NextResponse.json({ error: 'Internal Server Error' }, { status: 500 });
  }
}

/**
 * DELETE /api/annotations/[id]
 * Deletes an annotation by ID.
 */
export async function DELETE(
  _request: Request,
  { params }: { params: Promise<{ id: string }> }
): Promise<NextResponse> {
  try {
    const db = getDb();
    const { id } = await params;

    const existing = db.prepare('SELECT id FROM annotations WHERE id = ?').get(id);
    if (!existing) {
      return NextResponse.json({ error: 'Annotation not found' }, { status: 404 });
    }

    db.prepare('DELETE FROM annotations WHERE id = ?').run(id);

    return NextResponse.json({ success: true });
  } catch (error) {
    console.error('Error deleting annotation:', error);
    return NextResponse.json({ error: 'Internal Server Error' }, { status: 500 });
  }
}
