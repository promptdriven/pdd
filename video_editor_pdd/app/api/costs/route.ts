import { NextResponse } from "next/server";
import { getDb } from "@/lib/db";

export const dynamic = "force-dynamic";

export async function GET(): Promise<NextResponse> {
  try {
    const db = getDb();

    const rows = db.prepare(`
      SELECT stage,
             SUM(cost) as totalCost,
             SUM(inputTokens) as totalInputTokens,
             SUM(outputTokens) as totalOutputTokens,
             COUNT(*) as callCount
      FROM job_costs
      GROUP BY stage
      ORDER BY stage
    `).all() as Record<string, any>[];

    const totalRow = db.prepare('SELECT SUM(cost) as total FROM job_costs').get() as Record<string, any>;

    return NextResponse.json({
      totalCost: totalRow?.total ?? 0,
      byStage: rows.map((r) => ({
        stage: r.stage,
        totalCost: r.totalCost ?? 0,
        totalInputTokens: r.totalInputTokens ?? 0,
        totalOutputTokens: r.totalOutputTokens ?? 0,
        callCount: r.callCount ?? 0,
      })),
    });
  } catch (error) {
    console.error("Error fetching costs:", error);
    return NextResponse.json({ error: "Internal Server Error" }, { status: 500 });
  }
}
