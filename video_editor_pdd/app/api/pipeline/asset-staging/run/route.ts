import { NextRequest, NextResponse } from "next/server";
import fs from "fs";
import path from "path";
import { randomUUID } from "crypto";
import { getAppRemotionPublicDir, getProjectDir } from "@/lib/projects";

/**
 * POST /api/pipeline/asset-staging/run
 *
 * Copies VEO output files into the Remotion public directory so they can
 * be referenced by compositions at render time.
 */

interface AssetStagingBody {
  files?: string[];
}

export async function POST(request: NextRequest): Promise<NextResponse> {
  try {
    const veoOutputDir = path.join(getProjectDir(), "outputs", "veo");
    const remotionPublicDir = getAppRemotionPublicDir();
    const body = (await request.json().catch(() => ({}))) as AssetStagingBody;
    const files = body.files ?? [];

    const jobId = randomUUID();
    let staged = 0;

    for (const file of files) {
      const src = path.join(veoOutputDir, file);
      const dest = path.join(remotionPublicDir, file);

      if (!fs.existsSync(src)) continue;

      const destDir = path.dirname(dest);
      if (!fs.existsSync(destDir)) {
        fs.mkdirSync(destDir, { recursive: true });
      }

      if (!fs.existsSync(dest)) {
        fs.copyFileSync(src, dest);
        staged++;
      }
    }

    return NextResponse.json({ jobId, staged }, { status: 200 });
  } catch (err) {
    const message = err instanceof Error ? err.message : "Unknown error";
    return NextResponse.json(
      { error: message },
      { status: 500 }
    );
  }
}
