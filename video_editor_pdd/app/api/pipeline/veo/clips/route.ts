import fs from "fs";
import path from "path";
import { NextResponse } from "next/server";

import { loadProject } from "@/lib/project";
import {
  normalizeSpecDir,
  selectCanonicalVeoMarkdownSpec,
} from "@/lib/veo-spec-context";
import { resolveSectionHasVeoIntent } from "@/app/api/pipeline/_lib/script-visual-intent";

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
  specPath: string | null;
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
    const mainScriptPath = path.join(process.cwd(), "narrative", "main_script.md");
    let mainScriptContent: string | null = null;

    if (fs.existsSync(mainScriptPath)) {
      try {
        mainScriptContent = fs.readFileSync(mainScriptPath, "utf-8");
      } catch {
        mainScriptContent = null;
      }
    }

    const eligibleSections = sections.filter((section) => {
      if (!mainScriptContent) {
        return true;
      }

      return (
        resolveSectionHasVeoIntent(mainScriptContent, {
          id: section.id,
          label: section.label,
        }) !== false
      );
    });

    const clips: VeoClip[] = eligibleSections.map((section, idx) => {
      const clipId = section.id;
      const normalizedSpecDir = normalizeSpecDir(section.specDir ?? section.id);

      const clipPath = path.join(
        process.cwd(),
        "outputs",
        "veo",
        `${clipId}.mp4`
      );

      const prevSection = eligibleSections[idx - 1];
      // frameChainDeps exposes clean clip IDs for the UI (e.g. "cold_open")
      const frameChainDeps: string[] = prevSection ? [prevSection.id] : [];
      // depFilePaths are used internally for staleness checking only
      const depFilePaths: string[] = prevSection
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
      if (clipExists && depFilePaths.length > 0) {
        const clipTime = mtimeMs(clipPath) ?? 0;
        for (const dep of depFilePaths) {
          const depAbs = path.join(process.cwd(), dep);
          const depTime = mtimeMs(depAbs);
          if (depTime && depTime > clipTime) {
            stale = true;
            break;
          }
        }
      }

      let specPath: string | null = null;
      const specDir = path.join(process.cwd(), "specs", normalizedSpecDir);
      if (fs.existsSync(specDir)) {
        try {
          const markdownEntries = fs
            .readdirSync(specDir)
            .filter((file) => file.endsWith(".md") && !file.startsWith("AUDIT_"))
            .map((file) => ({
              path: path.posix.join("specs", normalizedSpecDir, file),
              content: fs.readFileSync(path.join(specDir, file), "utf-8"),
          }));
          const canonicalSpec = selectCanonicalVeoMarkdownSpec(markdownEntries);
          specPath = canonicalSpec?.path ?? null;
        } catch {
          specPath = null;
        }
      }

      return {
        id: clipId,
        sectionId: section.id,
        aspectRatio,
        status,
        stale,
        frameChainDeps,
        specPath,
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
