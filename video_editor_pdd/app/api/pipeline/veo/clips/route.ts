import fs from "fs";
import path from "path";
import { NextResponse } from "next/server";

import { loadProject } from "@/lib/project";

/**
 * GET /api/pipeline/veo/clips
 *
 * Returns a list of Veo clips with their generation status and frame-chain
 * dependencies, plus character reference portraits from project.json.
 */

type VeoClipStatus = "done" | "missing" | "error";

interface VeoClip {
  id: string;
  sectionId: string;
  aspectRatio: string;
  status: VeoClipStatus;
  stale: boolean;
  frameChainDeps: string[];
}

interface ReferencePortrait {
  id: string;
  label: string;
}

function mtimeMs(filePath: string): number | null {
  try {
    return fs.statSync(filePath).mtimeMs;
  } catch {
    return null;
  }
}

export async function GET(): Promise<NextResponse> {
  try {
    const config = loadProject();
    const sections = config.sections;
    const aspectRatio = config.veo.defaultAspectRatio;

    const clips: VeoClip[] = sections.map((section, idx) => {
      const clipId = section.id;

      const clipPath = path.join(
        process.cwd(),
        "outputs",
        "veo",
        `${clipId}.mp4`
      );

      const prevSection = sections[idx - 1];
      const deps: string[] = prevSection
        ? [
            path.join(
              "outputs",
              "veo",
              `${prevSection.id}_last_frame.png`
            ),
          ]
        : [];

      const clipExists = fs.existsSync(clipPath);
      const status: VeoClipStatus = clipExists ? "done" : "missing";

      let stale = false;
      if (clipExists && deps.length > 0) {
        const clipTime = mtimeMs(clipPath) ?? 0;
        for (const dep of deps) {
          const depAbs = path.join(process.cwd(), dep);
          const depTime = mtimeMs(depAbs);
          if (depTime && depTime > clipTime) {
            stale = true;
            break;
          }
        }
      }

      return {
        id: clipId,
        sectionId: section.id,
        aspectRatio,
        status,
        stale,
        frameChainDeps: deps,
      };
    });

    // Character references from project config
    const references: ReferencePortrait[] = (config.veo.references ?? []).map(
      (ref) => ({
        id: ref.id,
        label: ref.label,
      })
    );

    return NextResponse.json({ clips, references });
  } catch (err) {
    const message = err instanceof Error ? err.message : "Unknown error";
    return NextResponse.json(
      { error: message, clips: [], references: [] },
      { status: 500 }
    );
  }
}
