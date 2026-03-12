/**
 * Tests for lib/db.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/lib_db_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. getDb() returns a singleton, lazy-initializes, calls runMigrations + recoverCrashedJobs
 *   2. runMigrations() creates jobs, annotations, pipeline_status tables (idempotent)
 *   3. recoverCrashedJobs() marks running jobs as error
 *   4. DB path from DB_PATH env or cwd/pipeline.db
 *   5. "use server" directive at top
 *   6. WAL journal mode
 */

import BetterSqlite3, { type Database } from "better-sqlite3";
import fs from "fs";
import os from "os";
import path from "path";
import { runMigrations, recoverCrashedJobs } from "../lib/db";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Creates an in-memory better-sqlite3 database for isolated testing. */
function createTestDb(): Database {
  return new BetterSqlite3(":memory:");
}

/** Creates a temp-file-backed database; returns [db, filePath]. */
function createTempFileDb(): [Database, string] {
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "pdd-db-test-"));
  const dbPath = path.join(tmpDir, "test.db");
  const db = new BetterSqlite3(dbPath);
  return [db, tmpDir];
}

/** Returns column info for a table. */
function getColumns(
  db: Database,
  table: string
): { name: string; type: string; notnull: number; dflt_value: string | null; pk: number }[] {
  return db.pragma(`table_info(${table})`) as any[];
}

/** Returns all table names in the database. */
function getTableNames(db: Database): string[] {
  const rows = db
    .prepare("SELECT name FROM sqlite_master WHERE type='table' ORDER BY name")
    .all() as { name: string }[];
  return rows.map((r) => r.name);
}

// ---------------------------------------------------------------------------
// 1. runMigrations — table creation
// ---------------------------------------------------------------------------

describe("runMigrations", () => {
  let db: Database;

  beforeEach(() => {
    db = createTestDb();
  });

  afterEach(() => {
    db.close();
  });

  it("creates the jobs table", () => {
    runMigrations(db);
    const tables = getTableNames(db);
    expect(tables).toContain("jobs");
  });

  it("creates the annotations table", () => {
    runMigrations(db);
    const tables = getTableNames(db);
    expect(tables).toContain("annotations");
  });

  it("creates the pipeline_status table", () => {
    runMigrations(db);
    const tables = getTableNames(db);
    expect(tables).toContain("pipeline_status");
  });

  it("creates exactly four tables", () => {
    runMigrations(db);
    const tables = getTableNames(db);
    expect(tables).toHaveLength(4);
  });

  it("creates the job_costs table", () => {
    runMigrations(db);
    const tables = getTableNames(db);
    expect(tables).toContain("job_costs");
  });

  // --- jobs schema ---

  it("jobs table has correct columns", () => {
    runMigrations(db);
    const cols = getColumns(db, "jobs");
    const names = cols.map((c) => c.name);
    expect(names).toEqual([
      "id",
      "stage",
      "status",
      "progress",
      "error",
      "params",
      "logs",
      "createdAt",
      "updatedAt",
      "retryOf",
    ]);
  });

  it("jobs.id is TEXT PRIMARY KEY", () => {
    runMigrations(db);
    const cols = getColumns(db, "jobs");
    const idCol = cols.find((c) => c.name === "id")!;
    expect(idCol.type).toBe("TEXT");
    expect(idCol.pk).toBe(1);
  });

  it("jobs.progress is REAL", () => {
    runMigrations(db);
    const cols = getColumns(db, "jobs");
    const progressCol = cols.find((c) => c.name === "progress")!;
    expect(progressCol.type).toBe("REAL");
  });

  // --- annotations schema ---

  it("annotations table has correct columns", () => {
    runMigrations(db);
    const cols = getColumns(db, "annotations");
    const names = cols.map((c) => c.name);
    expect(names).toEqual([
      "id",
      "sectionId",
      "timestamp",
      "text",
      "videoFile",
      "drawingDataUrl",
      "compositeDataUrl",
      "analysis",
      "resolved",
      "resolveJobId",
      "createdAt",
      "inputMethod",
      "fixCommitSha",
    ]);
  });

  it("annotations.inputMethod has TEXT type with DEFAULT 'typed'", () => {
    runMigrations(db);
    const cols = getColumns(db, "annotations");
    const inputMethodCol = cols.find((c) => c.name === "inputMethod")!;
    expect(inputMethodCol.type).toBe("TEXT");
    expect(inputMethodCol.dflt_value).toBe("'typed'");
  });

  it("annotations.id is TEXT PRIMARY KEY", () => {
    runMigrations(db);
    const cols = getColumns(db, "annotations");
    const idCol = cols.find((c) => c.name === "id")!;
    expect(idCol.type).toBe("TEXT");
    expect(idCol.pk).toBe(1);
  });

  it("annotations.timestamp is REAL", () => {
    runMigrations(db);
    const cols = getColumns(db, "annotations");
    const tsCol = cols.find((c) => c.name === "timestamp")!;
    expect(tsCol.type).toBe("REAL");
  });

  it("annotations.resolved has INTEGER type with DEFAULT 0", () => {
    runMigrations(db);
    const cols = getColumns(db, "annotations");
    const resolvedCol = cols.find((c) => c.name === "resolved")!;
    expect(resolvedCol.type).toBe("INTEGER");
    expect(resolvedCol.dflt_value).toBe("0");
  });

  // --- pipeline_status schema ---

  it("pipeline_status table has correct columns", () => {
    runMigrations(db);
    const cols = getColumns(db, "pipeline_status");
    const names = cols.map((c) => c.name);
    expect(names).toEqual([
      "stage",
      "status",
      "lastJobId",
      "error",
      "updatedAt",
    ]);
  });

  it("pipeline_status.stage is TEXT PRIMARY KEY", () => {
    runMigrations(db);
    const cols = getColumns(db, "pipeline_status");
    const stageCol = cols.find((c) => c.name === "stage")!;
    expect(stageCol.type).toBe("TEXT");
    expect(stageCol.pk).toBe(1);
  });

  // --- job_costs schema ---

  it("job_costs table has correct columns", () => {
    runMigrations(db);
    const cols = getColumns(db, "job_costs");
    const names = cols.map((c) => c.name);
    expect(names).toEqual([
      "id",
      "jobId",
      "stage",
      "provider",
      "model",
      "inputTokens",
      "outputTokens",
      "cost",
      "createdAt",
    ]);
  });

  it("job_costs.id is TEXT PRIMARY KEY", () => {
    runMigrations(db);
    const cols = getColumns(db, "job_costs");
    const idCol = cols.find((c) => c.name === "id")!;
    expect(idCol.type).toBe("TEXT");
    expect(idCol.pk).toBe(1);
  });

  // --- jobs.retryOf column ---

  it("jobs table has retryOf column", () => {
    runMigrations(db);
    const cols = getColumns(db, "jobs");
    const retryOfCol = cols.find((c) => c.name === "retryOf");
    expect(retryOfCol).toBeDefined();
    expect(retryOfCol!.type).toBe("TEXT");
  });

  // --- idempotency ---

  it("is idempotent — running twice does not throw", () => {
    runMigrations(db);
    expect(() => runMigrations(db)).not.toThrow();
  });

  it("is idempotent — data is preserved across runs", () => {
    runMigrations(db);
    db.prepare(
      "INSERT INTO jobs (id, stage, status, createdAt, updatedAt) VALUES (?, ?, ?, ?, ?)"
    ).run("j1", "setup", "done", "2025-01-01T00:00:00Z", "2025-01-01T00:00:00Z");

    runMigrations(db);

    const row = db.prepare("SELECT * FROM jobs WHERE id = ?").get("j1") as any;
    expect(row).toBeDefined();
    expect(row.stage).toBe("setup");
  });
});

// ---------------------------------------------------------------------------
// 2. recoverCrashedJobs
// ---------------------------------------------------------------------------

describe("recoverCrashedJobs", () => {
  let db: Database;

  beforeEach(() => {
    db = createTestDb();
    runMigrations(db);
  });

  afterEach(() => {
    db.close();
  });

  it("marks running jobs as error", () => {
    db.prepare(
      "INSERT INTO jobs (id, stage, status, createdAt, updatedAt) VALUES (?, ?, ?, ?, ?)"
    ).run("j1", "tts-render", "running", "2025-01-01T00:00:00Z", "2025-01-01T00:00:00Z");

    recoverCrashedJobs(db);

    const row = db.prepare("SELECT * FROM jobs WHERE id = ?").get("j1") as any;
    expect(row.status).toBe("error");
  });

  it("sets error message to 'Server restarted during pipeline'", () => {
    db.prepare(
      "INSERT INTO jobs (id, stage, status, createdAt, updatedAt) VALUES (?, ?, ?, ?, ?)"
    ).run("j1", "render", "running", "2025-01-01T00:00:00Z", "2025-01-01T00:00:00Z");

    recoverCrashedJobs(db);

    const row = db.prepare("SELECT * FROM jobs WHERE id = ?").get("j1") as any;
    expect(row.error).toBe("Server restarted during pipeline");
  });

  it("sets updatedAt to an ISO 8601 string", () => {
    db.prepare(
      "INSERT INTO jobs (id, stage, status, createdAt, updatedAt) VALUES (?, ?, ?, ?, ?)"
    ).run("j1", "veo", "running", "2025-01-01T00:00:00Z", "2025-01-01T00:00:00Z");

    const before = new Date().toISOString();
    recoverCrashedJobs(db);
    const after = new Date().toISOString();

    const row = db.prepare("SELECT * FROM jobs WHERE id = ?").get("j1") as any;
    expect(row.updatedAt >= before).toBe(true);
    expect(row.updatedAt <= after).toBe(true);
  });

  it("does not affect jobs with status other than running", () => {
    db.prepare(
      "INSERT INTO jobs (id, stage, status, createdAt, updatedAt) VALUES (?, ?, ?, ?, ?)"
    ).run("j-done", "setup", "done", "2025-01-01T00:00:00Z", "2025-01-01T00:00:00Z");
    db.prepare(
      "INSERT INTO jobs (id, stage, status, createdAt, updatedAt) VALUES (?, ?, ?, ?, ?)"
    ).run("j-pending", "script", "pending", "2025-01-01T00:00:00Z", "2025-01-01T00:00:00Z");
    db.prepare(
      "INSERT INTO jobs (id, stage, status, createdAt, updatedAt) VALUES (?, ?, ?, ?, ?)"
    ).run("j-error", "render", "error", "2025-01-01T00:00:00Z", "2025-01-01T00:00:00Z");

    recoverCrashedJobs(db);

    const done = db.prepare("SELECT * FROM jobs WHERE id = ?").get("j-done") as any;
    const pending = db.prepare("SELECT * FROM jobs WHERE id = ?").get("j-pending") as any;
    const error = db.prepare("SELECT * FROM jobs WHERE id = ?").get("j-error") as any;

    expect(done.status).toBe("done");
    expect(pending.status).toBe("pending");
    expect(error.status).toBe("error");
    expect(error.error).toBeNull();
  });

  it("handles multiple running jobs at once", () => {
    for (let i = 0; i < 5; i++) {
      db.prepare(
        "INSERT INTO jobs (id, stage, status, createdAt, updatedAt) VALUES (?, ?, ?, ?, ?)"
      ).run(`j-${i}`, "render", "running", "2025-01-01T00:00:00Z", "2025-01-01T00:00:00Z");
    }

    recoverCrashedJobs(db);

    const rows = db.prepare("SELECT * FROM jobs WHERE status = 'error'").all() as any[];
    expect(rows).toHaveLength(5);
    for (const row of rows) {
      expect(row.error).toBe("Server restarted during pipeline");
    }
  });

  it("reconciles stale running pipeline_status rows to recovered job errors", () => {
    db.prepare(
      "INSERT INTO jobs (id, stage, status, createdAt, updatedAt) VALUES (?, ?, ?, ?, ?)"
    ).run("j-render", "render", "running", "2025-01-01T00:00:00Z", "2025-01-01T00:00:00Z");

    db.prepare(
      "INSERT INTO pipeline_status (stage, status, lastJobId, error, updatedAt) VALUES (?, ?, ?, ?, ?)"
    ).run("render", "running", "j-render", null, "2025-01-01T00:00:00Z");

    recoverCrashedJobs(db);

    const row = db.prepare("SELECT * FROM pipeline_status WHERE stage = ?").get("render") as any;
    expect(row.status).toBe("error");
    expect(row.lastJobId).toBe("j-render");
    expect(row.error).toBe("Server restarted during pipeline");
  });

  it("reconciles stale running pipeline_status rows to completed jobs", () => {
    db.prepare(
      "INSERT INTO jobs (id, stage, status, createdAt, updatedAt) VALUES (?, ?, ?, ?, ?)"
    ).run("j-render", "render", "done", "2025-01-01T00:00:00Z", "2025-01-01T00:00:00Z");

    db.prepare(
      "INSERT INTO pipeline_status (stage, status, lastJobId, error, updatedAt) VALUES (?, ?, ?, ?, ?)"
    ).run("render", "running", "j-render", "stale", "2025-01-01T00:00:00Z");

    recoverCrashedJobs(db);

    const row = db.prepare("SELECT * FROM pipeline_status WHERE stage = ?").get("render") as any;
    expect(row.status).toBe("done");
    expect(row.lastJobId).toBe("j-render");
    expect(row.error).toBeNull();
  });

  it("is a no-op when there are no running jobs", () => {
    db.prepare(
      "INSERT INTO jobs (id, stage, status, createdAt, updatedAt) VALUES (?, ?, ?, ?, ?)"
    ).run("j1", "setup", "done", "2025-01-01T00:00:00Z", "2025-01-01T00:00:00Z");

    expect(() => recoverCrashedJobs(db)).not.toThrow();

    const row = db.prepare("SELECT * FROM jobs WHERE id = ?").get("j1") as any;
    expect(row.status).toBe("done");
  });

  it("is a no-op when jobs table is empty", () => {
    expect(() => recoverCrashedJobs(db)).not.toThrow();
  });
});

// ---------------------------------------------------------------------------
// 3. getDb — singleton + initialization
// ---------------------------------------------------------------------------

describe("getDb", () => {
  let tmpDir: string;
  let dbPath: string;
  const originalDbPath = process.env.DB_PATH;

  beforeEach(() => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "pdd-getdb-test-"));
    dbPath = path.join(tmpDir, "test-pipeline.db");
    process.env.DB_PATH = dbPath;
    // Reset module to clear singleton (both module-level and globalThis)
    jest.resetModules();
    delete (globalThis as any).__pipelineDb;
  });

  afterEach(() => {
    if (originalDbPath === undefined) {
      delete process.env.DB_PATH;
    } else {
      process.env.DB_PATH = originalDbPath;
    }
    // Clean up temp files
    try {
      fs.rmSync(tmpDir, { recursive: true, force: true });
    } catch {
      // ignore cleanup errors
    }
  });

  it("returns a Database instance", () => {
    const { getDb } = require("../lib/db") as typeof import("../lib/db");
    const db = getDb();
    expect(db).toBeDefined();
    expect(typeof db.prepare).toBe("function");
    expect(typeof db.exec).toBe("function");
    db.close();
  });

  it("returns the same instance on subsequent calls (singleton)", () => {
    const { getDb } = require("../lib/db") as typeof import("../lib/db");
    const db1 = getDb();
    const db2 = getDb();
    expect(db1).toBe(db2);
    db1.close();
  });

  it("creates the database file at DB_PATH", () => {
    const { getDb } = require("../lib/db") as typeof import("../lib/db");
    const db = getDb();
    expect(fs.existsSync(dbPath)).toBe(true);
    db.close();
  });

  it("runs migrations on first call — tables exist", () => {
    const { getDb } = require("../lib/db") as typeof import("../lib/db");
    const db = getDb();
    const tables = getTableNames(db);
    expect(tables).toContain("jobs");
    expect(tables).toContain("annotations");
    expect(tables).toContain("pipeline_status");
    expect(tables).toContain("job_costs");
    db.close();
  });

  it("runs crash recovery on first call — running jobs are marked error", () => {
    // Pre-create the database with a running job
    const setupDb = new BetterSqlite3(dbPath);
    setupDb.exec(`
      CREATE TABLE IF NOT EXISTS jobs (
        id TEXT PRIMARY KEY, stage TEXT, status TEXT, progress REAL,
        error TEXT, params TEXT, createdAt TEXT, updatedAt TEXT
      );
      INSERT INTO jobs (id, stage, status, createdAt, updatedAt)
      VALUES ('pre-j1', 'render', 'running', '2025-01-01T00:00:00Z', '2025-01-01T00:00:00Z');
    `);
    setupDb.close();

    const { getDb } = require("../lib/db") as typeof import("../lib/db");
    const db = getDb();

    const row = db.prepare("SELECT * FROM jobs WHERE id = ?").get("pre-j1") as any;
    expect(row.status).toBe("error");
    expect(row.error).toBe("Server restarted during pipeline");
    db.close();
  });

  it("enables WAL journal mode", () => {
    const { getDb } = require("../lib/db") as typeof import("../lib/db");
    const db = getDb();
    const result = db.pragma("journal_mode") as { journal_mode: string }[];
    expect(result[0].journal_mode).toBe("wal");
    db.close();
  });

  it("uses DB_PATH env variable when set", () => {
    const customPath = path.join(tmpDir, "custom.db");
    process.env.DB_PATH = customPath;
    jest.resetModules();
    const { getDb } = require("../lib/db") as typeof import("../lib/db");
    const db = getDb();
    expect(fs.existsSync(customPath)).toBe(true);
    db.close();
  });
});

// ---------------------------------------------------------------------------
// 4. Source file structure checks
// ---------------------------------------------------------------------------

describe("lib/db.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    sourceCode = fs.readFileSync(
      path.join(__dirname, "..", "lib", "db.ts"),
      "utf-8"
    );
  });

  it('guards against client-side usage with server-only require', () => {
    // The module uses try { require('server-only') } catch {} to prevent
    // client-side imports while gracefully handling test environments where
    // the server-only package may not be available.
    expect(sourceCode).toMatch(/require\s*\(\s*['"]server-only['"]\s*\)/);
  });

  it('does not use "use server" directive (functions are sync, not Server Actions)', () => {
    const lines = sourceCode.split("\n").filter((l) => l.trim().length > 0);
    expect(lines[0].trim()).not.toMatch(/^["']use server["'];?$/);
  });

  it("exports getDb function", () => {
    expect(sourceCode).toMatch(/export\s+function\s+getDb/);
  });

  it("exports runMigrations function", () => {
    expect(sourceCode).toMatch(/export\s+function\s+runMigrations/);
  });

  it("exports recoverCrashedJobs function", () => {
    expect(sourceCode).toMatch(/export\s+function\s+recoverCrashedJobs/);
  });

  it("persists singleton database handles in a global map for HMR resilience", () => {
    expect(sourceCode).toMatch(/Map<string,\s*Database>/);
    expect(sourceCode).toMatch(/__pipelineDbs/);
  });

  it("persists singleton on globalThis for HMR resilience", () => {
    expect(sourceCode).toMatch(/globalThis/);
    expect(sourceCode).toMatch(/__pipelineDb/);
  });

  it("uses CREATE TABLE IF NOT EXISTS for idempotent migrations", () => {
    const matches = sourceCode.match(/CREATE TABLE IF NOT EXISTS/g);
    expect(matches).not.toBeNull();
    expect(matches!.length).toBe(4);
  });

  it("uses db.exec for DDL statements in runMigrations", () => {
    expect(sourceCode).toMatch(/db\.exec\s*\(/);
  });

  it("uses db.prepare for the crash recovery UPDATE", () => {
    expect(sourceCode).toMatch(/db\.prepare\s*\(/);
  });

  it("references DB_PATH environment variable", () => {
    expect(sourceCode).toMatch(/process\.env\.DB_PATH/);
  });

  it("references getProjectDbPath as the default database location", () => {
    expect(sourceCode).toMatch(/getProjectDbPath/);
  });

  it("sets WAL journal mode via pragma", () => {
    expect(sourceCode).toMatch(/pragma\s*\(\s*["']journal_mode\s*=\s*WAL["']\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 5. Integration — full data round-trip
// ---------------------------------------------------------------------------

describe("integration: data round-trip through migrated schema", () => {
  let db: Database;

  beforeEach(() => {
    db = createTestDb();
    runMigrations(db);
  });

  afterEach(() => {
    db.close();
  });

  it("can insert and retrieve a job row", () => {
    const now = new Date().toISOString();
    db.prepare(
      "INSERT INTO jobs (id, stage, status, progress, error, params, createdAt, updatedAt) VALUES (?, ?, ?, ?, ?, ?, ?, ?)"
    ).run("job-1", "tts-render", "running", 0.5, null, '{"key":"val"}', now, now);

    const row = db.prepare("SELECT * FROM jobs WHERE id = ?").get("job-1") as any;
    expect(row.id).toBe("job-1");
    expect(row.stage).toBe("tts-render");
    expect(row.status).toBe("running");
    expect(row.progress).toBe(0.5);
    expect(row.error).toBeNull();
    expect(row.params).toBe('{"key":"val"}');
  });

  it("can insert and retrieve an annotation row with JSON analysis", () => {
    const analysis = JSON.stringify({
      severity: "major",
      fixType: "remotion",
      technicalAssessment: "Text clipped",
      suggestedFixes: ["Fix it"],
      confidence: 0.9,
    });
    const now = new Date().toISOString();
    db.prepare(
      "INSERT INTO annotations (id, sectionId, timestamp, text, videoFile, drawingDataUrl, compositeDataUrl, analysis, resolved, resolveJobId, createdAt) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)"
    ).run("a-1", "section-1", 3.14, "Issue here", "video.mp4", null, null, analysis, 0, null, now);

    const row = db.prepare("SELECT * FROM annotations WHERE id = ?").get("a-1") as any;
    expect(row.id).toBe("a-1");
    expect(row.timestamp).toBeCloseTo(3.14);
    expect(row.resolved).toBe(0);
    const parsed = JSON.parse(row.analysis);
    expect(parsed.severity).toBe("major");
    expect(parsed.confidence).toBe(0.9);
  });

  it("annotations.resolved defaults to 0 when not specified", () => {
    db.prepare(
      "INSERT INTO annotations (id, sectionId, timestamp, text, createdAt) VALUES (?, ?, ?, ?, ?)"
    ).run("a-2", "s1", 1.0, "note", new Date().toISOString());

    const row = db.prepare("SELECT resolved FROM annotations WHERE id = ?").get("a-2") as any;
    expect(row.resolved).toBe(0);
  });

  it("can insert and retrieve a pipeline_status row", () => {
    const now = new Date().toISOString();
    db.prepare(
      "INSERT INTO pipeline_status (stage, status, lastJobId, error, updatedAt) VALUES (?, ?, ?, ?, ?)"
    ).run("render", "running", "job-42", null, now);

    const row = db.prepare("SELECT * FROM pipeline_status WHERE stage = ?").get("render") as any;
    expect(row.stage).toBe("render");
    expect(row.status).toBe("running");
    expect(row.lastJobId).toBe("job-42");
    expect(row.error).toBeNull();
  });

  it("enforces PRIMARY KEY on jobs.id", () => {
    const now = new Date().toISOString();
    db.prepare(
      "INSERT INTO jobs (id, stage, status, createdAt, updatedAt) VALUES (?, ?, ?, ?, ?)"
    ).run("dup", "setup", "done", now, now);

    expect(() =>
      db.prepare(
        "INSERT INTO jobs (id, stage, status, createdAt, updatedAt) VALUES (?, ?, ?, ?, ?)"
      ).run("dup", "render", "pending", now, now)
    ).toThrow();
  });

  it("enforces PRIMARY KEY on annotations.id", () => {
    const now = new Date().toISOString();
    db.prepare(
      "INSERT INTO annotations (id, sectionId, timestamp, text, createdAt) VALUES (?, ?, ?, ?, ?)"
    ).run("ann-dup", "s1", 0, "a", now);

    expect(() =>
      db.prepare(
        "INSERT INTO annotations (id, sectionId, timestamp, text, createdAt) VALUES (?, ?, ?, ?, ?)"
      ).run("ann-dup", "s2", 1, "b", now)
    ).toThrow();
  });

  it("enforces PRIMARY KEY on pipeline_status.stage", () => {
    const now = new Date().toISOString();
    db.prepare(
      "INSERT INTO pipeline_status (stage, status, updatedAt) VALUES (?, ?, ?)"
    ).run("render", "done", now);

    expect(() =>
      db.prepare(
        "INSERT INTO pipeline_status (stage, status, updatedAt) VALUES (?, ?, ?)"
      ).run("render", "running", now)
    ).toThrow();
  });
});
