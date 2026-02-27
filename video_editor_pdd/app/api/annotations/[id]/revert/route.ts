import { NextResponse } from "next/server";
import { getDb } from "@/lib/db";
import { revertFix } from "@/lib/git";

export const dynamic = "force-dynamic";

type RouteParams = { params: Promise<{ id: string }> };

export async function POST(_request: Request, { params }: RouteParams) {
  const { id: annotationId } = await params;
  const db = getDb();

  try {
    const row = db
      .prepare("SELECT fixCommitSha, sectionId FROM annotations WHERE id = ?")
      .get(annotationId) as { fixCommitSha: string | null; sectionId: string } | undefined;

    if (!row) {
      return NextResponse.json({ error: "Annotation not found" }, { status: 404 });
    }

    if (!row.fixCommitSha) {
      return NextResponse.json({ error: "No fix commit to revert" }, { status: 404 });
    }

    const revertSha = revertFix(row.fixCommitSha);

    // Clear the fixCommitSha and mark as unresolved
    db.prepare(
      "UPDATE annotations SET fixCommitSha = NULL, resolved = 0 WHERE id = ?"
    ).run(annotationId);

    return NextResponse.json({
      revertCommitSha: revertSha,
      annotationId,
      sectionId: row.sectionId,
    });
  } catch (error) {
    console.error("Failed to revert fix:", error);
    return NextResponse.json({ error: "Failed to revert fix" }, { status: 500 });
  }
}
