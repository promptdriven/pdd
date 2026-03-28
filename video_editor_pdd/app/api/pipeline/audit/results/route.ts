import { NextRequest, NextResponse } from "next/server";
import path from "path";
import fs from "fs";
import { loadProject } from "@/lib/project";
import { resolveSectionVisuals } from "@/lib/composition-timing";
import { resolveRenderedAuditSampleWindow } from "@/lib/audit-timing";
import { getProjectDir } from "@/lib/projects";
import {
  resolveSectionSpecDir,
  resolveSectionSpecFile,
  toSectionSpecPath,
} from "../_lib/spec-paths";
import { resolveSectionCompositionIds } from "@/app/api/pipeline/_lib/composition-manifest";

type SpecAuditResult = {
  specName: string;
  verdict: "PASS" | "FAIL" | "SKIP" | "WARN";
  summary: string;
  finding?: string;
  specPath?: string;
  playbackWindow?: {
    startSeconds: number;
    endSeconds: number;
    sampleSeconds: number;
    source: "timestamp" | "frame-range" | "fallback";
  };
};

type AuditSectionResult = {
  sectionId: string;
  sectionLabel: string;
  passCount: number;
  warnCount: number;
  failCount: number;
  status: "done" | "pending" | "error";
  specs: SpecAuditResult[];
};

const DATA_POINTS_JSON_RE =
  /(?:^|\n)##\s*Data Points(?:\s+JSON)?\s*(?:\r?\n)+```json\s*([\s\S]+?)\s*```/i;

function parseAuditMarkdown(content: string): {
  verdict: "PASS" | "FAIL" | "SKIP" | "WARN";
  summary: string;
} {
  const verdictMatch = content.match(/## Verdict\s+(\w+)/i);
  const summaryMatch = content.match(/## Summary\s+([\s\S]+)/i);

  if (!verdictMatch || !summaryMatch) {
    throw new Error("Invalid audit markdown format");
  }

  const normalizedVerdict = verdictMatch[1].toLowerCase();
  const verdict =
    normalizedVerdict === "pass"
      ? ("PASS" as const)
      : normalizedVerdict === "warn"
        ? ("WARN" as const)
      : normalizedVerdict === "skip"
        ? ("SKIP" as const)
        : ("FAIL" as const);
  const summary = summaryMatch[1].trim();

  return { verdict, summary };
}

function parseDataPointsJson(content: string): Record<string, unknown> | null {
  const match = DATA_POINTS_JSON_RE.exec(content);
  if (!match?.[1]) {
    return null;
  }

  try {
    const parsed = JSON.parse(match[1]);
    return parsed && typeof parsed === "object" && !Array.isArray(parsed)
      ? (parsed as Record<string, unknown>)
      : null;
  } catch {
    return null;
  }
}

function isEmbeddedChildSpec(content: string): boolean {
  const dataPoints = parseDataPointsJson(content);
  if (!dataPoints) {
    return false;
  }

  const rawParent =
    dataPoints.embeddedIn ?? dataPoints.compositeOver ?? dataPoints.usedIn;
  return typeof rawParent === "string" && rawParent.trim().length > 0;
}

export async function GET(_request: NextRequest): Promise<NextResponse> {
  try {
    const config = loadProject();
    const results: AuditSectionResult[] = [];

    for (const section of config.sections) {
      const specDir = resolveSectionSpecDir(section.specDir);
      const files = fs.existsSync(specDir) ? fs.readdirSync(specDir) : [];
      const rawSpecFiles = files.filter(
        (f) => f.endsWith(".md") && !f.startsWith("AUDIT_")
      );
      const auditFiles = files.filter(
        (f) => f.endsWith(".md") && f.startsWith("AUDIT_")
      );
      const configuredCompositionIds = resolveSectionCompositionIds(section);
      const usesCompositionManifest = configuredCompositionIds.length > 0;
      const renderableVisuals =
        usesCompositionManifest
          ? resolveSectionVisuals(
              getProjectDir(),
              section,
              configuredCompositionIds
            )
              .filter((visual) => Boolean(visual.specPath))
              .map((visual) => ({
                specName: visual.specBaseName,
                specPath: visual.specPath as string,
              }))
          : rawSpecFiles.map((specFile) => ({
              specName: path.basename(specFile, ".md"),
              specPath: resolveSectionSpecFile(section.specDir, specFile),
            }));
      const renderableSpecNames = new Set(
        renderableVisuals.map((visual) => visual.specName)
      );
      const fallbackAuditVisuals = auditFiles
        .map((auditFile) => {
          const specName = path
            .basename(auditFile, ".md")
            .replace(/^AUDIT_/, "");
          return {
            specName,
            specPath: resolveSectionSpecFile(section.specDir, `${specName}.md`),
          };
        })
        .filter((visual) => !renderableSpecNames.has(visual.specName));
      const visualsToRead = [...renderableVisuals, ...fallbackAuditVisuals];
      const fps = config.render?.fps ?? 30;

      const specResultsByName = new Map<string, SpecAuditResult>();
      let passCount = 0;
      let warnCount = 0;
      let failCount = 0;
      let missingAuditCount = 0;
      let existingRenderableAuditCount = 0;
      const missingRenderableVisuals: Array<{
        specName: string;
        specPath: string;
      }> = [];

      for (const visual of visualsToRead) {
        const specName = visual.specName;
        const auditPath = resolveSectionSpecFile(
          section.specDir,
          `AUDIT_${specName}.md`
        );
        if (!fs.existsSync(auditPath)) {
          if (usesCompositionManifest && renderableSpecNames.has(specName)) {
            missingRenderableVisuals.push(visual);
          } else {
            missingAuditCount++;
          }
          continue;
        }
        if (usesCompositionManifest && renderableSpecNames.has(specName)) {
          existingRenderableAuditCount++;
        }
        try {
          const content = fs.readFileSync(auditPath, "utf-8");
          const { verdict, summary } = parseAuditMarkdown(content);

          if (verdict === "PASS") passCount++;
          else if (verdict === "WARN") warnCount++;
          else if (verdict === "FAIL") failCount++;

          const specSourcePath = visual.specPath;
          const safeSpecPath = toSectionSpecPath(section.specDir, `${specName}.md`);
          const specExists = fs.existsSync(specSourcePath);
          const playbackWindow = specExists
            ? resolveRenderedAuditSampleWindow(
                fs.readFileSync(specSourcePath, "utf-8"),
                {
                  projectDir: getProjectDir(),
                  specPath: specSourcePath,
                  section,
                  sectionDurationSeconds: section.durationSeconds,
                  fps,
                }
              )
            : undefined;

          specResultsByName.set(specName, {
            specName,
            verdict,
            summary,
            finding: verdict === "FAIL" ? summary : undefined,
            specPath: specExists ? safeSpecPath : undefined,
            playbackWindow,
          });
        } catch {
          specResultsByName.set(specName, {
            specName,
            verdict: "FAIL",
            summary: "Error parsing audit report",
            finding: "Error parsing audit report",
          });
          failCount++;
        }
      }

      const hasPartialManifestAuditCoverage =
        usesCompositionManifest &&
        existingRenderableAuditCount > 0 &&
        missingRenderableVisuals.length > 0;

      if (hasPartialManifestAuditCoverage) {
        for (const visual of missingRenderableVisuals) {
          const specSourcePath = visual.specPath;
          const safeSpecPath = toSectionSpecPath(section.specDir, `${visual.specName}.md`);
          const specExists = fs.existsSync(specSourcePath);
          const playbackWindow = specExists
            ? resolveRenderedAuditSampleWindow(
                fs.readFileSync(specSourcePath, "utf-8"),
                {
                  projectDir: getProjectDir(),
                  specPath: specSourcePath,
                  section,
                  sectionDurationSeconds: section.durationSeconds,
                  fps,
                }
              )
            : undefined;

          specResultsByName.set(visual.specName, {
            specName: visual.specName,
            verdict: "FAIL",
            summary:
              "Missing audit report for active visual. Re-run audit for this section.",
            finding:
              "Missing audit report for active visual. Re-run audit for this section.",
            specPath: specExists ? safeSpecPath : undefined,
            playbackWindow,
          });
          failCount++;
        }
      }

      const knownSpecNames = new Set(specResultsByName.keys());
      for (const specFile of rawSpecFiles) {
        const specName = path.basename(specFile, ".md");
        if (knownSpecNames.has(specName)) {
          continue;
        }
        if (usesCompositionManifest && renderableSpecNames.has(specName)) {
          continue;
        }

        const specSourcePath = resolveSectionSpecFile(section.specDir, specFile);
        if (fs.existsSync(specSourcePath)) {
          try {
            const specContent = fs.readFileSync(specSourcePath, "utf-8");
            if (isEmbeddedChildSpec(specContent)) {
              continue;
            }
          } catch {
            // Fall through to a visible SKIP entry for unreadable specs.
          }
        }

        specResultsByName.set(specName, {
          specName,
          verdict: "SKIP",
          summary:
            "Not audited as a standalone visual because this spec does not map to a rendered composition or directly staged media slot.",
          specPath: toSectionSpecPath(section.specDir, specFile),
        });
      }

      const rawSpecNames = rawSpecFiles.map((specFile) =>
        path.basename(specFile, ".md")
      );
      const orderedSpecNames = [
        ...rawSpecNames,
        ...Array.from(specResultsByName.keys()).filter(
          (specName) => !rawSpecNames.includes(specName)
        ),
      ];
      const specs = orderedSpecNames
        .map((specName) => specResultsByName.get(specName))
        .filter((spec): spec is SpecAuditResult => Boolean(spec));

      const status: AuditSectionResult["status"] =
        hasPartialManifestAuditCoverage
          ? "error"
          : missingAuditCount > 0 ||
              (usesCompositionManifest &&
                existingRenderableAuditCount === 0 &&
                missingRenderableVisuals.length > 0)
          ? "pending"
          : "done";

      results.push({
        sectionId: section.id,
        sectionLabel: section.label,
        passCount,
        warnCount,
        failCount,
        status,
        specs,
      });
    }

    return NextResponse.json({ sections: results }, { status: 200 });
  } catch (err) {
    console.error("Error reading audit results:", err);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}
