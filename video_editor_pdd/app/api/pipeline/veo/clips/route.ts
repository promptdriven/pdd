import fs from "fs";
import path from "path";
import { NextResponse } from "next/server";

import { loadProject } from "@/lib/project";
import {
  listResolvedVeoClipSpecs,
  normalizeSpecDir,
  selectCanonicalVeoMarkdownSpec,
} from "@/lib/veo-spec-context";
import { resolveSectionHasVeoIntent } from "@/app/api/pipeline/_lib/script-visual-intent";
import { getProjectDir } from "@/lib/projects";
import { resolveVeoFrameChainPlan } from "../_lib/frame-chains";

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

type ResolvedClipEntry = {
  id: string;
  sectionId: string;
  specPath: string | null;
};

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
    const mainScriptPath = path.join(getProjectDir(), "narrative", "main_script.md");
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

    const resolvedClips: ResolvedClipEntry[] = eligibleSections.flatMap((section) => {
      const normalizedSpecDir = normalizeSpecDir(section.specDir ?? section.id);
      const specDir = path.join(getProjectDir(), "specs", normalizedSpecDir);

      if (fs.existsSync(specDir)) {
        try {
          const markdownEntries = fs
            .readdirSync(specDir)
            .filter((file) => file.endsWith(".md") && !file.startsWith("AUDIT_"))
            .map((file) => ({
              path: path.posix.join("specs", normalizedSpecDir, file),
              content: fs.readFileSync(path.join(specDir, file), "utf-8"),
            }));
          const specClips = listResolvedVeoClipSpecs(markdownEntries);
          if (specClips.length > 0) {
            return specClips.map((clip) => ({
              id: clip.id,
              sectionId: section.id,
              specPath: clip.path,
            }));
          }

          const canonicalSpec = selectCanonicalVeoMarkdownSpec(markdownEntries);
          return [
            {
              id: section.id,
              sectionId: section.id,
              specPath: canonicalSpec?.path ?? null,
            },
          ];
        } catch {
          return [
            {
              id: section.id,
              sectionId: section.id,
              specPath: null,
            },
          ];
        }
      }

      return [
        {
          id: section.id,
          sectionId: section.id,
          specPath: null,
        },
      ];
    });

    const chainPlan = resolveVeoFrameChainPlan(
      getProjectDir(),
      resolvedClips.map((clip) => clip.id),
      config.veo
    );

    const clips: VeoClip[] = resolvedClips.map((clip) => {
      const clipId = clip.id;
      const clipPath = path.join(
        getProjectDir(),
        "outputs",
        "veo",
        `${clipId}.mp4`
      );
      const clipChain = chainPlan.get(clipId);
      const frameChainDeps: string[] = clipChain?.previousClipId
        ? [clipChain.previousClipId]
        : [];
      const depFilePaths: string[] = clipChain?.previousClipId
        ? [path.join("outputs", "veo", `${clipChain.previousClipId}_last_frame.png`)]
        : [];

      const clipExists = fs.existsSync(clipPath);
      const status: VeoClipStatus = clipExists ? "done" : "missing";

      let stale = false;
      if (clipExists && depFilePaths.length > 0) {
        const clipTime = mtimeMs(clipPath) ?? 0;
        for (const dep of depFilePaths) {
          const depAbs = path.join(getProjectDir(), dep);
          const depTime = mtimeMs(depAbs);
          if (depTime && depTime > clipTime) {
            stale = true;
            break;
          }
        }
      }

      return {
        id: clipId,
        sectionId: clip.sectionId,
        aspectRatio,
        status,
        stale,
        frameChainDeps,
        specPath: clip.specPath,
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
