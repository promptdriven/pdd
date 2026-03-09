import { NextRequest, NextResponse } from "next/server";
import path from "path";
import fs from "fs";
import { loadProject } from "@/lib/project";
import { resolveRenderedAuditSampleWindow } from "@/lib/audit-timing";
import {
  resolveSectionSpecDir,
  resolveSectionSpecFile,
  toSectionSpecPath,
} from "../_lib/spec-paths";

type SpecAuditResult = {
  specName: string;
  verdict: "PASS" | "FAIL";
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
  failCount: number;
  status: "done" | "pending" | "error";
  specs: SpecAuditResult[];
};

function parseAuditMarkdown(content: string): {
  verdict: "PASS" | "FAIL";
  summary: string;
} {
  const verdictMatch = content.match(/## Verdict\s+(\w+)/i);
  const summaryMatch = content.match(/## Summary\s+([\s\S]+)/i);

  if (!verdictMatch || !summaryMatch) {
    throw new Error("Invalid audit markdown format");
  }

  const verdict =
    verdictMatch[1].toLowerCase() === "pass" ? ("PASS" as const) : ("FAIL" as const);
  const summary = summaryMatch[1].trim();

  return { verdict, summary };
}

export async function GET(_request: NextRequest): Promise<NextResponse> {
  try {
    const config = loadProject();
    const results: AuditSectionResult[] = [];

    for (const section of config.sections) {
      const specDir = resolveSectionSpecDir(section.specDir);
      const files = fs.existsSync(specDir) ? fs.readdirSync(specDir) : [];

      const auditFiles = files.filter((f) => f.startsWith("AUDIT_"));
      const specFiles = files.filter(
        (f) => f.endsWith(".md") && !f.startsWith("AUDIT_")
      );
      const fps = config.render?.fps ?? 30;

      const specs: SpecAuditResult[] = [];
      let passCount = 0;
      let failCount = 0;

      for (const auditFile of auditFiles) {
        const auditPath = path.join(specDir, auditFile);
        try {
          const content = fs.readFileSync(auditPath, "utf-8");
          const { verdict, summary } = parseAuditMarkdown(content);

          const specName = auditFile
            .replace(/^AUDIT_/, "")
            .replace(/\.md$/, "");

          if (verdict === "PASS") passCount++;
          else failCount++;

          const specSourcePath = resolveSectionSpecFile(
            section.specDir,
            `${specName}.md`
          );
          const safeSpecPath = toSectionSpecPath(section.specDir, `${specName}.md`);
          const specExists = fs.existsSync(specSourcePath);
          const playbackWindow = specExists
            ? resolveRenderedAuditSampleWindow(
                fs.readFileSync(specSourcePath, "utf-8"),
                {
                  projectDir: process.cwd(),
                  specPath: specSourcePath,
                  section,
                  sectionSpecFiles: specFiles,
                  sectionDurationSeconds: section.durationSeconds,
                  fps,
                }
              )
            : undefined;

          specs.push({
            specName,
            verdict,
            summary,
            finding: verdict === "FAIL" ? summary : undefined,
            specPath: specExists ? safeSpecPath : undefined,
            playbackWindow,
          });
        } catch {
          const specName = auditFile
            .replace(/^AUDIT_/, "")
            .replace(/\.md$/, "");
          specs.push({
            specName,
            verdict: "FAIL",
            summary: "Error parsing audit report",
            finding: "Error parsing audit report",
          });
          failCount++;
        }
      }

      const status: AuditSectionResult["status"] =
        auditFiles.length === 0 && specFiles.length > 0
          ? "pending"
          : "done";

      results.push({
        sectionId: section.id,
        sectionLabel: section.label,
        passCount,
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
