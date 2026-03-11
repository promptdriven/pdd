/**
 * Integration tests for the Remotion/Claude environment.
 *
 * TDD plan: write failing tests first, then implement fixes.
 *
 * Steps:
 *   1. Bundle path resolves to an existing file
 *   2. Required Remotion assets exist
 *   3. renderSection() completes for cold_open  (slow, ~60s)
 *   4. preview-fixes API returns real Claude output (requires Claude CLI, ~30s)
 *   5. Full batch resolve completes and resolves the annotation (~5min)
 *
 * Run individual groups:
 *   npx jest tests/integration/test_remotion_environment.ts --testNamePattern="bundle|assets"
 *   npx jest tests/integration/test_remotion_environment.ts --testNamePattern="renderSection" --testTimeout=120000
 *   npx jest tests/integration/test_remotion_environment.ts --testNamePattern="preview-fixes"
 *   npx jest tests/integration/test_remotion_environment.ts --testNamePattern="resolve-batch"
 */

import fs from "fs";
import os from "os";
import path from "path";
import { execSync } from "child_process";

/**
 * Retry helper for flaky tests that depend on Remotion child processes.
 * Remotion renders spawn HTTP servers sensitive to parallel I/O contention.
 */
async function withRetry<T>(fn: () => Promise<T>, retries = 2): Promise<T> {
  for (let attempt = 0; ; attempt++) {
    try {
      return await fn();
    } catch (err) {
      if (attempt >= retries) throw err;
      // Wait before retrying to let other workers release resources
      await new Promise((r) => setTimeout(r, 3000));
    }
  }
}

type ProjectSectionFixture = {
  id: string;
  label: string;
  compositionId: string;
  durationSeconds?: number;
  offsetSeconds?: number;
};

type ProjectFixture = {
  sections: ProjectSectionFixture[];
} & Record<string, unknown>;

const PROJECT_ROOT = process.cwd();
const PROJECT_DIR = path.join(PROJECT_ROOT, "projects", "integration-test");
const PROJECT_JSON_PATH = path.join(PROJECT_DIR, "project.json");
const REMOTION_DIR = path.join(PROJECT_ROOT, "remotion");
const ROOT_TSX_PATH = path.join(REMOTION_DIR, "src", "remotion", "Root.tsx");
const ACTIVE_PROJECT_ID = "integration-test";
const ORIGINAL_PROJECT_ID = process.env.VIDEO_EDITOR_PROJECT_ID;
const ORIGINAL_PROJECT_JSON = fs.readFileSync(PROJECT_JSON_PATH, "utf-8");
const GENERATED_FILE_BACKUPS = new Map<string, string | null>();

function ensureTestProjectDurations(project: ProjectFixture): ProjectFixture {
  let offsetSeconds = 0;

  return {
    ...project,
    sections: project.sections.map((section) => {
      const durationSeconds =
        typeof section.durationSeconds === "number" && section.durationSeconds > 0
          ? section.durationSeconds
          : 12;

      const nextSection = {
        ...section,
        durationSeconds,
        offsetSeconds,
      };
      offsetSeconds += durationSeconds;
      return nextSection;
    }),
  };
}

function backupGeneratedFiles(project: ProjectFixture): void {
  GENERATED_FILE_BACKUPS.set(
    ROOT_TSX_PATH,
    fs.existsSync(ROOT_TSX_PATH) ? fs.readFileSync(ROOT_TSX_PATH, "utf-8") : null
  );

  for (const section of project.sections) {
    const wrapperPath = getSectionWrapperPath(section.id);
    GENERATED_FILE_BACKUPS.set(
      wrapperPath,
      fs.existsSync(wrapperPath) ? fs.readFileSync(wrapperPath, "utf-8") : null
    );
  }
}

function restoreGeneratedFiles(): void {
  for (const [filePath, originalContent] of GENERATED_FILE_BACKUPS.entries()) {
    if (originalContent === null) {
      if (fs.existsSync(filePath)) {
        fs.unlinkSync(filePath);
      }
      continue;
    }

    fs.mkdirSync(path.dirname(filePath), { recursive: true });
    fs.writeFileSync(filePath, originalContent, "utf-8");
  }
}

function loadActiveProjectFixture(): ProjectFixture {
  return JSON.parse(fs.readFileSync(PROJECT_JSON_PATH, "utf-8")) as ProjectFixture;
}

function getSectionWrapperPath(sectionId: string): string {
  return path.join(REMOTION_DIR, "src", "remotion", sectionId, "index.tsx");
}

function getSectionWrapperSource(sectionId: string): string {
  return fs.readFileSync(getSectionWrapperPath(sectionId), "utf-8");
}

function extractStaticFileAssets(source: string): string[] {
  return Array.from(source.matchAll(/staticFile\((["'`])(.+?)\1\)/g), (match) => match[2]);
}

beforeAll(() => {
  process.env.VIDEO_EDITOR_PROJECT_ID = ACTIVE_PROJECT_ID;

  const project = ensureTestProjectDurations(
    JSON.parse(ORIGINAL_PROJECT_JSON) as ProjectFixture
  );

  backupGeneratedFiles(project);
  fs.writeFileSync(PROJECT_JSON_PATH, JSON.stringify(project, null, 2), "utf-8");

  execSync(
    `python3 "${path.join(PROJECT_ROOT, "scripts", "generate_section_compositions.py")}" --project-dir "${PROJECT_DIR}" --remotion-dir "${REMOTION_DIR}" --force`,
    {
    cwd: PROJECT_ROOT,
    stdio: "pipe",
    }
  );

  execSync("npx remotion bundle src/index.ts --out build", {
    cwd: REMOTION_DIR,
    stdio: "pipe",
    timeout: 120_000,
  });
});

afterAll(() => {
  if (ORIGINAL_PROJECT_ID) {
    process.env.VIDEO_EDITOR_PROJECT_ID = ORIGINAL_PROJECT_ID;
  } else {
    delete process.env.VIDEO_EDITOR_PROJECT_ID;
  }

  fs.writeFileSync(PROJECT_JSON_PATH, ORIGINAL_PROJECT_JSON, "utf-8");
  restoreGeneratedFiles();
});

const ACTIVE_PROJECT = loadActiveProjectFixture();
const ACTIVE_SECTIONS = ACTIVE_PROJECT.sections;
const FIX_TARGET_SECTION = ACTIVE_SECTIONS[0];
const RENDER_SMOKE_SECTION =
  ACTIVE_SECTIONS.find((section) => {
    const wrapperPath = getSectionWrapperPath(section.id);
    if (!fs.existsSync(wrapperPath)) return false;
    return extractStaticFileAssets(getSectionWrapperSource(section.id)).some((asset) =>
      asset.endsWith(".mp4"),
    );
  }) ?? FIX_TARGET_SECTION;

// ---------------------------------------------------------------------------
// Step 1 — Bundle path
// ---------------------------------------------------------------------------

describe("Remotion bundle", () => {
  it("build/index.html exists and is non-empty", () => {
    const bundlePath = path.join(PROJECT_ROOT, "remotion", "build", "index.html");
    expect(fs.existsSync(bundlePath)).toBe(true);
    expect(fs.statSync(bundlePath).size).toBeGreaterThan(0);
  });

  it("REMOTION_BUNDLE_PATH env var is set in .env.local", () => {
    const envPath = path.join(PROJECT_ROOT, ".env.local");
    const content = fs.existsSync(envPath) ? fs.readFileSync(envPath, "utf-8") : "";
    expect(content).toMatch(/REMOTION_BUNDLE_PATH/);
  });

  it(".env.local REMOTION_BUNDLE_PATH points to the build directory", () => {
    const envPath = path.join(PROJECT_ROOT, ".env.local");
    const content = fs.existsSync(envPath) ? fs.readFileSync(envPath, "utf-8") : "";
    expect(content).toMatch(/REMOTION_BUNDLE_PATH=.*remotion\/build/);
  });

  it("NEXT_DISABLE_FAST_REFRESH is set in .env.local", () => {
    const envPath = path.join(PROJECT_ROOT, ".env.local");
    const content = fs.existsSync(envPath) ? fs.readFileSync(envPath, "utf-8") : "";
    expect(content).toMatch(/NEXT_DISABLE_FAST_REFRESH=1/);
  });

  it("remotion/package.json has a build script", () => {
    const pkgPath = path.join(PROJECT_ROOT, "remotion", "package.json");
    expect(fs.existsSync(pkgPath)).toBe(true);
    const pkg = JSON.parse(fs.readFileSync(pkgPath, "utf-8"));
    expect(pkg.scripts?.build).toBeDefined();
    expect(pkg.scripts.build).toMatch(/remotion bundle/);
  });
});

// ---------------------------------------------------------------------------
// Step 2 — Required assets
// ---------------------------------------------------------------------------

describe("Remotion assets", () => {
  for (const section of ACTIVE_SECTIONS) {
    it(`${section.id} narration WAV exists`, () => {
      const wav = path.join(PROJECT_ROOT, "remotion", "public", section.id, "narration.wav");
      expect(fs.existsSync(wav)).toBe(true);
      expect(fs.statSync(wav).size).toBeGreaterThan(0);
    });

    it(`${section.id} section wrapper source exists`, () => {
      expect(fs.existsSync(getSectionWrapperPath(section.id))).toBe(true);
    });

    it(`${section.id} wrapper staticFile assets exist`, () => {
      const assets = extractStaticFileAssets(getSectionWrapperSource(section.id));
      expect(assets.length).toBeGreaterThan(0);

      for (const asset of assets) {
        const assetPath = path.join(PROJECT_ROOT, "remotion", "public", asset);
        expect(fs.existsSync(assetPath)).toBe(true);
        expect(fs.statSync(assetPath).size).toBeGreaterThan(0);
      }
    });
  }

  it("Root.tsx registers every active project composition", () => {
    const rootPath = path.join(PROJECT_ROOT, "remotion/src/remotion/Root.tsx");
    const content = fs.readFileSync(rootPath, "utf-8");

    for (const section of ACTIVE_SECTIONS) {
      expect(content).toContain(`id="${section.compositionId}"`);
    }
  });
});

// ---------------------------------------------------------------------------
// Step 3 — renderSection() smoke test (slow, ~60s)
// ---------------------------------------------------------------------------

describe("renderSection", () => {
  // Remotion serveUrl must be the DIRECTORY containing index.html, not the file itself
  const bundlePath = path.join(PROJECT_ROOT, "remotion", "build");
  const outPath = path.join(
    os.tmpdir(),
    `${RENDER_SMOKE_SECTION.id}_test_${Date.now()}.mp4`,
  );

  beforeAll(() => {
    // Set the bundle path so renderSection uses the pre-compiled bundle
    process.env.REMOTION_BUNDLE_PATH = bundlePath;
  });

  afterAll(() => {
    delete process.env.REMOTION_BUNDLE_PATH;
    // Clean up rendered file if it exists
    if (fs.existsSync(outPath)) {
      fs.unlinkSync(outPath);
    }
  });

  it(
    `renders ${RENDER_SMOKE_SECTION.compositionId} to a non-empty MP4 file`,
    async () => {
      await withRetry(async () => {
        // Clean up any partial output from previous attempt
        if (fs.existsSync(outPath)) fs.unlinkSync(outPath);

        const { renderSection } = await import("@/lib/render");

        await renderSection(RENDER_SMOKE_SECTION.compositionId, outPath, (progress) => {
          expect(typeof progress.percent).toBe("number");
          expect(progress.percent).toBeGreaterThanOrEqual(0);
          expect(progress.percent).toBeLessThanOrEqual(100);
        });

        expect(fs.existsSync(outPath)).toBe(true);
        expect(fs.statSync(outPath).size).toBeGreaterThan(0);
      });
    },
    360_000 // 6-minute timeout (accounts for up to 3 attempts)
  );
});

// ---------------------------------------------------------------------------
// Step 4 — preview-fixes API returns real Claude output (~30s)
// ---------------------------------------------------------------------------

describe("preview-fixes API", () => {
  const tmpDbPath = path.join(os.tmpdir(), `pdd-preview-test-${Date.now()}.db`);
  const annId = `test-preview-ann-${Date.now()}`;

  beforeAll(() => {
    // Use a temp DB so we don't pollute the real pipeline.db
    process.env.DB_PATH = tmpDbPath;
    process.env.REMOTION_BUNDLE_PATH = path.join(
      PROJECT_ROOT,
      "remotion",
      "build"
    );
  });

  afterAll(() => {
    delete process.env.DB_PATH;
    delete process.env.REMOTION_BUNDLE_PATH;
    // Remove the temp DB
    for (const ext of ["", "-shm", "-wal"]) {
      const p = tmpDbPath + ext;
      if (fs.existsSync(p)) fs.unlinkSync(p);
    }
  });

  it(
    "returns a preview with non-empty description and valid confidence",
    async () => {
      // Seed a meaningful annotation into the temp DB
      const { getDb } = await import("@/lib/db");
      const db = getDb();

      db.prepare(
        `INSERT OR REPLACE INTO annotations
         (id, sectionId, timestamp, text, analysis, resolved, createdAt)
         VALUES (?, ?, ?, ?, ?, 0, ?)`
      ).run(
        annId,
        FIX_TARGET_SECTION.id,
        5.0,
        `Change the primary background accent in ${FIX_TARGET_SECTION.label} to #00FF00.`,
        JSON.stringify({
          severity: "minor",
          fixType: "remotion",
          confidence: 0.85,
          technicalAssessment:
            "The current color treatment should shift to a clearly visible green accent.",
          suggestedFixes: ["Update the background accent color to #00FF00"],
        }),
        new Date().toISOString()
      );

      try {
        const { NextRequest } = await import("next/server");
        const { POST } = await import(
          "@/app/api/sections/[id]/preview-fixes/route"
        );

        const req = new NextRequest(
          `http://localhost/api/sections/${FIX_TARGET_SECTION.id}/preview-fixes`,
          {
            method: "POST",
            headers: { "Content-Type": "application/json" },
            body: JSON.stringify({ annotationIds: [annId] }),
          }
        );

        const res = await POST(req, { params: { id: FIX_TARGET_SECTION.id } });
        expect(res.status).toBe(200);

        const body = await res.json();
        expect(body).toHaveProperty("previews");
        expect(body.previews.length).toBeGreaterThan(0);

        const preview = body.previews[0];
        expect(preview.annotationId).toBe(annId);
        expect(preview.fixType).toBe("remotion");

        // Claude must return a non-empty description
        expect(preview.preview).toBeTruthy();
        expect(preview.preview.length).toBeGreaterThan(10);

        // Claude must return a valid confidence score
        expect(typeof preview.confidence).toBe("number");
        expect(preview.confidence).toBeGreaterThan(0);
      } finally {
        db.prepare("DELETE FROM annotations WHERE id = ?").run(annId);
      }
    },
    90_000 // 90s timeout for Claude CLI call
  );
});

// ---------------------------------------------------------------------------
// Step 5 — Full batch resolve completes and resolves the annotation (~5min)
// ---------------------------------------------------------------------------

describe("resolve-batch pipeline", () => {
  const tmpDbPath = path.join(os.tmpdir(), `pdd-batch-test-${Date.now()}.db`);
  const annId = `test-batch-ann-${Date.now()}`;

  /** Poll until the job reaches 'done' or 'error', or timeout fires. */
  async function waitForJob(
    jobId: string,
    timeoutMs: number
  ): Promise<"done" | "error"> {
    const { getDb } = await import("@/lib/db");
    const db = getDb();
    const deadline = Date.now() + timeoutMs;

    while (Date.now() < deadline) {
      const row = db
        .prepare("SELECT status FROM jobs WHERE id = ? LIMIT 1")
        .get(jobId) as { status: string } | undefined;

      if (row?.status === "done") return "done";
      if (row?.status === "error") return "error";

      await new Promise((resolve) => setTimeout(resolve, 2_000));
    }

    throw new Error(`Job ${jobId} did not complete within ${timeoutMs}ms`);
  }

  beforeAll(() => {
    process.env.DB_PATH = tmpDbPath;
    process.env.REMOTION_BUNDLE_PATH = path.join(
      PROJECT_ROOT,
      "remotion",
      "build"
    );
    process.env.PDD_DETERMINISTIC_PIPELINE = "1";
  });

  afterAll(() => {
    delete process.env.DB_PATH;
    delete process.env.REMOTION_BUNDLE_PATH;
    delete process.env.PDD_DETERMINISTIC_PIPELINE;
    for (const ext of ["", "-shm", "-wal"]) {
      const p = tmpDbPath + ext;
      if (fs.existsSync(p)) fs.unlinkSync(p);
    }
  });

  it(
    "completes a remotion fix and resolves the annotation",
    async () => {
      const { getDb } = await import("@/lib/db");
      const db = getDb();

      // Seed annotation
      db.prepare(
        `INSERT OR REPLACE INTO annotations
         (id, sectionId, timestamp, text, analysis, resolved, createdAt)
         VALUES (?, ?, ?, ?, ?, 0, ?)`
      ).run(
        annId,
        FIX_TARGET_SECTION.id,
        5.0,
        `Change the primary background accent in ${FIX_TARGET_SECTION.label} to #00FF00.`,
        JSON.stringify({
          severity: "minor",
          fixType: "remotion",
          confidence: 0.85,
          technicalAssessment:
            "The current color treatment should shift to a clearly visible green accent.",
          suggestedFixes: ["Update the background accent color to #00FF00"],
        }),
        new Date().toISOString()
      );

      try {
        const { NextRequest } = await import("next/server");
        const { POST } = await import(
          "@/app/api/sections/[id]/resolve-batch/route"
        );

        const req = new NextRequest(
          `http://localhost/api/sections/${FIX_TARGET_SECTION.id}/resolve-batch`,
          {
            method: "POST",
            headers: { "Content-Type": "application/json" },
            body: JSON.stringify({ annotationIds: [annId] }),
          }
        );

        const res = await POST(req, { params: { id: FIX_TARGET_SECTION.id } });
        expect(res.status).toBe(200);

        const { jobId } = await res.json();
        expect(jobId).toBeTruthy();

        // Wait for the job to complete (max 4 minutes)
        const status = await waitForJob(jobId, 240_000);
        const jobRow = db
          .prepare("SELECT status, error, logs FROM jobs WHERE id = ?")
          .get(jobId) as
            | { status: string; error: string | null; logs: string | null }
            | undefined;

        expect(jobRow).toBeDefined();
        if (status !== "done") {
          throw new Error(
            `resolve-batch job failed: ${JSON.stringify(
              { status, error: jobRow?.error, logs: jobRow?.logs },
              null,
              2,
            )}`,
          );
        }

        // Check the annotation was updated
        const row = db
          .prepare("SELECT fixCommitSha, resolved FROM annotations WHERE id = ?")
          .get(annId) as { fixCommitSha: string | null; resolved: number } | undefined;

        expect(row).toBeDefined();
        expect(row!.resolved).toBe(1);
        if (row!.fixCommitSha !== null) {
          expect(row!.fixCommitSha).toBeTruthy();
        }
      } finally {
        db.prepare("DELETE FROM annotations WHERE id = ?").run(annId);
      }
    },
    300_000 // 5-minute timeout
  );
});
