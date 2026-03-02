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
 *   5. Full batch resolve sets fixCommitSha on the annotation (~5min)
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

// ---------------------------------------------------------------------------
// Step 1 — Bundle path
// ---------------------------------------------------------------------------

describe("Remotion bundle", () => {
  it("build/index.html exists and is non-empty", () => {
    const bundlePath = path.join(process.cwd(), "remotion", "build", "index.html");
    expect(fs.existsSync(bundlePath)).toBe(true);
    expect(fs.statSync(bundlePath).size).toBeGreaterThan(0);
  });

  it("REMOTION_BUNDLE_PATH env var is set in .env.local", () => {
    const envPath = path.join(process.cwd(), ".env.local");
    const content = fs.existsSync(envPath) ? fs.readFileSync(envPath, "utf-8") : "";
    expect(content).toMatch(/REMOTION_BUNDLE_PATH/);
  });

  it(".env.local REMOTION_BUNDLE_PATH points to the build directory", () => {
    const envPath = path.join(process.cwd(), ".env.local");
    const content = fs.existsSync(envPath) ? fs.readFileSync(envPath, "utf-8") : "";
    expect(content).toMatch(/REMOTION_BUNDLE_PATH=.*remotion\/build/);
  });

  it("NEXT_DISABLE_FAST_REFRESH is set in .env.local", () => {
    const envPath = path.join(process.cwd(), ".env.local");
    const content = fs.existsSync(envPath) ? fs.readFileSync(envPath, "utf-8") : "";
    expect(content).toMatch(/NEXT_DISABLE_FAST_REFRESH=1/);
  });

  it("remotion/package.json has a build script", () => {
    const pkgPath = path.join(process.cwd(), "remotion", "package.json");
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
  it("cold_open narration WAV exists", () => {
    const wav = path.join(process.cwd(), "remotion/public/cold_open/narration.wav");
    expect(fs.existsSync(wav)).toBe(true);
    expect(fs.statSync(wav).size).toBeGreaterThan(0);
  });

  it("VEO cold_open clip exists", () => {
    const mp4 = path.join(process.cwd(), "remotion/public/veo/cold_open.mp4");
    expect(fs.existsSync(mp4)).toBe(true);
    expect(fs.statSync(mp4).size).toBeGreaterThan(0);
  });

  it("ColdOpenSection.tsx source exists", () => {
    const tsx = path.join(process.cwd(), "remotion/src/remotion/ColdOpenSection.tsx");
    expect(fs.existsSync(tsx)).toBe(true);
  });

  it("Root.tsx registers ColdOpenSection composition", () => {
    const rootPath = path.join(process.cwd(), "remotion/src/remotion/Root.tsx");
    const content = fs.readFileSync(rootPath, "utf-8");
    expect(content).toMatch(/id=["']ColdOpenSection["']/);
  });
});

// ---------------------------------------------------------------------------
// Step 3 — renderSection() smoke test (slow, ~60s)
// ---------------------------------------------------------------------------

describe("renderSection", () => {
  // Remotion serveUrl must be the DIRECTORY containing index.html, not the file itself
  const bundlePath = path.join(process.cwd(), "remotion", "build");
  const outPath = path.join(os.tmpdir(), `cold_open_test_${Date.now()}.mp4`);

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
    "renders ColdOpenSection to a non-empty MP4 file",
    async () => {
      const { renderSection } = await import("@/lib/render");

      await renderSection("ColdOpenSection", outPath, (progress) => {
        // Ensure progress callbacks fire with valid values
        expect(typeof progress.percent).toBe("number");
        expect(progress.percent).toBeGreaterThanOrEqual(0);
        expect(progress.percent).toBeLessThanOrEqual(100);
      });

      expect(fs.existsSync(outPath)).toBe(true);
      expect(fs.statSync(outPath).size).toBeGreaterThan(0);
    },
    120_000 // 2-minute timeout
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
      process.cwd(),
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
        "cold_open",
        5.0,
        "Subtitle font size 96px causes text to clip the right edge of the frame",
        JSON.stringify({
          severity: "minor",
          fixType: "remotion",
          confidence: 0.85,
          technicalAssessment:
            "The subtitle fontSize prop is too large; text overflows the composition width",
          suggestedFixes: ["Reduce fontSize from 96 to 64 or lower"],
        }),
        new Date().toISOString()
      );

      try {
        const { NextRequest } = await import("next/server");
        const { POST } = await import(
          "@/app/api/sections/[id]/preview-fixes/route"
        );

        const req = new NextRequest(
          "http://localhost/api/sections/cold_open/preview-fixes",
          {
            method: "POST",
            headers: { "Content-Type": "application/json" },
            body: JSON.stringify({ annotationIds: [annId] }),
          }
        );

        const res = await POST(req, { params: { id: "cold_open" } });
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
// Step 5 — Full batch resolve sets fixCommitSha (~5min)
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
      process.cwd(),
      "remotion",
      "build"
    );
  });

  afterAll(() => {
    delete process.env.DB_PATH;
    delete process.env.REMOTION_BUNDLE_PATH;
    for (const ext of ["", "-shm", "-wal"]) {
      const p = tmpDbPath + ext;
      if (fs.existsSync(p)) fs.unlinkSync(p);
    }
  });

  it(
    "completes a remotion fix and sets fixCommitSha on the annotation",
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
        "cold_open",
        5.0,
        "Subtitle font size 96px causes text to clip the right edge of the frame",
        JSON.stringify({
          severity: "minor",
          fixType: "remotion",
          confidence: 0.85,
          technicalAssessment:
            "The subtitle fontSize prop is too large; text overflows the composition width",
          suggestedFixes: ["Reduce fontSize from 96 to 64 or lower"],
        }),
        new Date().toISOString()
      );

      try {
        const { NextRequest } = await import("next/server");
        const { POST } = await import(
          "@/app/api/sections/[id]/resolve-batch/route"
        );

        const req = new NextRequest(
          "http://localhost/api/sections/cold_open/resolve-batch",
          {
            method: "POST",
            headers: { "Content-Type": "application/json" },
            body: JSON.stringify({ annotationIds: [annId] }),
          }
        );

        const res = await POST(req, { params: { id: "cold_open" } });
        expect(res.status).toBe(200);

        const { jobId } = await res.json();
        expect(jobId).toBeTruthy();

        // Wait for the job to complete (max 4 minutes)
        const status = await waitForJob(jobId, 240_000);
        expect(status).toBe("done");

        // Check the annotation was updated
        const row = db
          .prepare("SELECT fixCommitSha, resolved FROM annotations WHERE id = ?")
          .get(annId) as { fixCommitSha: string | null; resolved: number } | undefined;

        expect(row).toBeDefined();
        // fixCommitSha is set when git is available and Claude edits a file
        expect(row!.fixCommitSha).toBeTruthy();
      } finally {
        db.prepare("DELETE FROM annotations WHERE id = ?").run(annId);
      }
    },
    300_000 // 5-minute timeout
  );
});
