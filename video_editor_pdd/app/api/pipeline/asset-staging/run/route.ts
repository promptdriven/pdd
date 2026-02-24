import { NextRequest, NextResponse } from "next/server";
import fs from "fs";
import path from "path";
import { randomUUID } from "crypto";

/**
 * POST /api/pipeline/asset-staging/run
 *
 * Copies VEO output files into the Remotion public directory so they can
 * be referenced by compositions at render time.
 */

interface AssetStagingBody {
  files?: string[];
}

const VEO_OUTPUT_DIR = path.join(process.cwd(), "outputs", "veo");
const REMOTION_PUBLIC_DIR = path.join(process.cwd(), "remotion", "public");

export async function POST(request: NextRequest): Promise<NextResponse> {
  try {
    const body = (await request.json().catch(() => ({}))) as AssetStagingBody;
    const files = body.files ?? [];

    const jobId = randomUUID();
    let staged = 0;

    for (const file of files) {
      const src = path.join(VEO_OUTPUT_DIR, file);
      const dest = path.join(REMOTION_PUBLIC_DIR, file);

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
