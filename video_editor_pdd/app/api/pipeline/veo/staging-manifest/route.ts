import { NextResponse } from "next/server";
import fs from "fs";
import path from "path";
import { getAppRemotionPublicDir, getProjectDir } from "@/lib/projects";

/**
 * GET /api/pipeline/veo/staging-manifest
 *
 * Returns the asset staging manifest: a list of files that are expected
 * by the Remotion compositions and whether they are present in the
 * Remotion public/veo directory.
 */

interface StagingManifestEntry {
  filename: string;
  expected: boolean;
  present: boolean;
}

function loadManifest(veoOutputDir: string): string[] {
  const candidates = [
    path.join(veoOutputDir, "staging.json"),
    path.join(veoOutputDir, "staging-manifest.json"),
    path.join(veoOutputDir, "manifest.json"),
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
  if (fs.existsSync(veoOutputDir)) {
    try {
      return fs
        .readdirSync(veoOutputDir)
        .filter((f) => f.endsWith(".mp4") || f.endsWith(".webm"));
    } catch {
      return [];
    }
  }

  return [];
}

export async function GET(): Promise<NextResponse> {
  try {
    const veoOutputDir = path.join(getProjectDir(), "outputs", "veo");
    const remotionPublicDir = path.join(getAppRemotionPublicDir(), "veo");
    const filenames = loadManifest(veoOutputDir);

    const entries: StagingManifestEntry[] = filenames.map((filename) => {
      const presentInPublic = fs.existsSync(
        path.join(remotionPublicDir, filename)
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
