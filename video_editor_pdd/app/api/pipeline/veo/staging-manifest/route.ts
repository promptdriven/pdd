import { NextResponse } from "next/server";
import fs from "fs";
import path from "path";

/**
 * GET /api/pipeline/veo/staging-manifest
 *
 * Returns the asset staging manifest: a list of files that are expected
 * by the Remotion compositions and whether they are present in the
 * Remotion public directory.
 */

interface StagingManifestEntry {
  filename: string;
  expected: boolean;
  present: boolean;
}

const VEO_OUTPUT_DIR = path.join(process.cwd(), "outputs", "veo");
const REMOTION_PUBLIC_DIR = path.join(process.cwd(), "remotion", "public");

function loadManifest(): string[] {
  const candidates = [
    path.join(VEO_OUTPUT_DIR, "staging.json"),
    path.join(VEO_OUTPUT_DIR, "staging-manifest.json"),
    path.join(VEO_OUTPUT_DIR, "manifest.json"),
  ];

  for (const p of candidates) {
    if (fs.existsSync(p)) {
      try {
        const raw = fs.readFileSync(p, "utf-8");
        const parsed = JSON.parse(raw);
        if (Array.isArray(parsed)) return parsed;
        if (Array.isArray(parsed.files)) return parsed.files;
      } catch {
        continue;
      }
    }
  }

  // Fallback: scan VEO output directory for MP4 files
  if (fs.existsSync(VEO_OUTPUT_DIR)) {
    try {
      return fs
        .readdirSync(VEO_OUTPUT_DIR)
        .filter((f) => f.endsWith(".mp4") || f.endsWith(".webm"));
    } catch {
      return [];
    }
  }

  return [];
}

export async function GET(): Promise<NextResponse> {
  try {
    const filenames = loadManifest();

    const entries: StagingManifestEntry[] = filenames.map((filename) => {
      const presentInPublic = fs.existsSync(
        path.join(REMOTION_PUBLIC_DIR, filename)
      );

      return {
        filename,
        expected: true,
        present: presentInPublic,
      };
    });

    return NextResponse.json(entries);
  } catch (err) {
    const message = err instanceof Error ? err.message : "Unknown error";
    return NextResponse.json(
      { error: message },
      { status: 500 }
    );
  }
}
