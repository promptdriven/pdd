import { NextResponse } from "next/server";
import { getDb } from "@/lib/db";
import { getFixDiff } from "@/lib/git";

export const dynamic = "force-dynamic";

type RouteParams = { params: { id: string } };

export async function GET(_request: Request, { params }: RouteParams) {
  const annotationId = params.id;
  const db = getDb();

  try {
    const row = db
      .prepare("SELECT fixCommitSha FROM annotations WHERE id = ?")
      .get(annotationId) as { fixCommitSha: string | null } | undefined;

    if (!row) {
      return NextResponse.json({ error: "Annotation not found" }, { status: 404 });
    }

    if (!row.fixCommitSha) {
      return NextResponse.json({ error: "No fix commit associated with this annotation" }, { status: 404 });
    }

    const diff = getFixDiff(row.fixCommitSha);
    return NextResponse.json({ commitSha: row.fixCommitSha, diff });
  } catch (error) {
    console.error("Failed to get fix diff:", error);
    return NextResponse.json({ error: "Failed to retrieve diff" }, { status: 500 });
  }
}
