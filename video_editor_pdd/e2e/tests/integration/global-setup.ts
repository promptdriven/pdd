import fs from 'fs';
import path from 'path';
import BetterSqlite3 from 'better-sqlite3';

const PROJECT_ROOT = path.resolve(__dirname, '..', '..', '..');
const FIXTURE_DIR = path.join(PROJECT_ROOT, 'e2e', 'fixtures', 'integration');
const ACTIVE_PROJECT_DIR = path.join(PROJECT_ROOT, 'projects', 'integration-test');

const PROJECT_JSON = path.join(ACTIVE_PROJECT_DIR, 'project.json');
const MAIN_SCRIPT = path.join(ACTIVE_PROJECT_DIR, 'narrative', 'main_script.md');
const PIPELINE_DB = path.join(ACTIVE_PROJECT_DIR, 'pipeline.db');
const OUTPUTS_DIR = path.join(ACTIVE_PROJECT_DIR, 'outputs');
const SPECS_DIR = path.join(ACTIVE_PROJECT_DIR, 'specs');
const SPECS_BACKUP = SPECS_DIR + '.integration-backup';
const ACTIVE_PROJECT_REMOTION = path.join(ACTIVE_PROJECT_DIR, 'remotion');

const REMOTION_DIR = path.join(PROJECT_ROOT, 'remotion');
const REMOTION_SRC = path.join(REMOTION_DIR, 'src', 'remotion');
const REMOTION_PUBLIC = path.join(REMOTION_DIR, 'public');
const REMOTION_BUILD = path.join(REMOTION_DIR, 'build');
const REMOTION_BUILD_BACKUP = REMOTION_BUILD + '.integration-backup';
const ROOT_TSX = path.join(REMOTION_SRC, 'Root.tsx');

const BACKUP_SUFFIX = '.integration-backup';
const REMOTION_SNAPSHOT = path.join(PROJECT_ROOT, '.integration-remotion-snapshot.json');

function backupIfExists(filePath: string): void {
  if (fs.existsSync(filePath)) {
    fs.copyFileSync(filePath, filePath + BACKUP_SUFFIX);
  }
}

export default function globalSetup(): void {
  fs.mkdirSync(ACTIVE_PROJECT_DIR, { recursive: true });

  // Back up existing files
  backupIfExists(PROJECT_JSON);
  backupIfExists(MAIN_SCRIPT);
  backupIfExists(PIPELINE_DB);
  backupIfExists(PIPELINE_DB + '-wal');
  backupIfExists(PIPELINE_DB + '-shm');

  // Copy fixture project.json
  fs.copyFileSync(path.join(FIXTURE_DIR, 'project.json'), PROJECT_JSON);

  // Copy fixture main_script.md
  fs.mkdirSync(path.dirname(MAIN_SCRIPT), { recursive: true });
  fs.copyFileSync(path.join(FIXTURE_DIR, 'main_script.md'), MAIN_SCRIPT);

  // Delete pipeline.db and WAL files to start fresh
  for (const suffix of ['', '-wal', '-shm']) {
    const f = PIPELINE_DB + suffix;
    if (fs.existsSync(f)) {
      fs.unlinkSync(f);
    }
  }

  // Create fresh pipeline.db with schema and seed manual stages as done.
  const db = new BetterSqlite3(PIPELINE_DB);
  db.pragma('journal_mode = WAL');
  db.exec(`
    CREATE TABLE IF NOT EXISTS jobs (
      id TEXT PRIMARY KEY,
      stage TEXT,
      status TEXT,
      progress REAL,
      error TEXT,
      params TEXT,
      logs TEXT DEFAULT '',
      createdAt TEXT,
      updatedAt TEXT,
      retryOf TEXT
    );
    CREATE TABLE IF NOT EXISTS annotations (
      id TEXT PRIMARY KEY,
      sectionId TEXT,
      timestamp REAL,
      text TEXT,
      videoFile TEXT,
      drawingDataUrl TEXT,
      compositeDataUrl TEXT,
      analysis TEXT,
      resolved INTEGER DEFAULT 0,
      resolveJobId TEXT,
      createdAt TEXT,
      inputMethod TEXT DEFAULT 'typed',
      fixCommitSha TEXT
    );
    CREATE TABLE IF NOT EXISTS pipeline_status (
      stage TEXT PRIMARY KEY,
      status TEXT,
      lastJobId TEXT,
      error TEXT,
      updatedAt TEXT
    );
    CREATE TABLE IF NOT EXISTS job_costs (
      id TEXT PRIMARY KEY,
      jobId TEXT,
      stage TEXT,
      provider TEXT,
      model TEXT,
      inputTokens INTEGER DEFAULT 0,
      outputTokens INTEGER DEFAULT 0,
      cost REAL DEFAULT 0,
      createdAt TEXT,
      FOREIGN KEY (jobId) REFERENCES jobs(id)
    );
  `);

  const now = new Date().toISOString();
  const seedJob = db.prepare(
    `INSERT INTO jobs (id, stage, status, progress, error, params, logs, createdAt, updatedAt)
     VALUES (?, ?, 'done', 100, NULL, '{}', '', ?, ?)`,
  );
  const seedStatus = db.prepare(
    `INSERT INTO pipeline_status (stage, status, lastJobId, error, updatedAt)
     VALUES (?, 'done', ?, NULL, ?)`,
  );

  // Seed stages that can't or shouldn't run through runPipelineStage:
  // - 'setup' / 'script': manual UI stages with no executors.
  // Other stages (tts-render, render) now use runPipelineStage and update
  // pipeline_status correctly, so they no longer need seeding.
  for (const stage of ['setup', 'script']) {
    const jobId = `seed-${stage}`;
    seedJob.run(jobId, stage, now, now);
    seedStatus.run(stage, jobId, now);
  }

  db.close();

  // Clean outputs directory
  if (fs.existsSync(OUTPUTS_DIR)) {
    fs.rmSync(OUTPUTS_DIR, { recursive: true, force: true });
  }

  // Remove any stale project-local remotion tree from earlier buggy runs.
  if (fs.existsSync(ACTIVE_PROJECT_REMOTION)) {
    fs.rmSync(ACTIVE_PROJECT_REMOTION, { recursive: true, force: true });
  }

  // Back up and clean specs directory so Claude CLI doesn't waste time
  // reading stale spec files from previous projects.
  if (fs.existsSync(SPECS_DIR)) {
    if (fs.existsSync(SPECS_BACKUP)) {
      fs.rmSync(SPECS_BACKUP, { recursive: true, force: true });
    }
    fs.renameSync(SPECS_DIR, SPECS_BACKUP);
  }
  fs.mkdirSync(SPECS_DIR, { recursive: true });

  // ── Remotion: back up files and snapshot for teardown cleanup ────────
  backupIfExists(ROOT_TSX);
  // Write a clean Root.tsx so the compositions stage generates only
  // test project sections (not leftover compositions from the real project).
  fs.mkdirSync(path.dirname(ROOT_TSX), { recursive: true });
  fs.writeFileSync(
    ROOT_TSX,
    [
      'import React from "react";',
      'import { Composition } from "remotion";',
      '',
      'export const RemotionRoot: React.FC = () => {',
      '  return (',
      '    <>',
      '    </>',
      '  );',
      '};',
      '',
    ].join('\n'),
  );
  if (fs.existsSync(REMOTION_BUILD)) {
    if (fs.existsSync(REMOTION_BUILD_BACKUP)) {
      fs.rmSync(REMOTION_BUILD_BACKUP, { recursive: true, force: true });
    }
    fs.renameSync(REMOTION_BUILD, REMOTION_BUILD_BACKUP);
  }

  // Snapshot existing files in remotion/src/remotion/ so teardown can
  // remove anything that stages 6-8 generate during the test.
  const remotionSrcEntries = fs.existsSync(REMOTION_SRC)
    ? fs.readdirSync(REMOTION_SRC)
    : [];
  fs.writeFileSync(REMOTION_SNAPSHOT, JSON.stringify(remotionSrcEntries));

  // Snapshot existing dirs in remotion/public/ for teardown cleanup.
  const publicEntries = fs.existsSync(REMOTION_PUBLIC)
    ? fs.readdirSync(REMOTION_PUBLIC)
    : [];
  fs.writeFileSync(
    path.join(PROJECT_ROOT, '.integration-remotion-public-snapshot.json'),
    JSON.stringify(publicEntries),
  );

  // Clean remotion/public/veo/ to remove stale Veo clips from previous runs
  // that could pollute animation-only sections with video overlays.
  const veoPublicDir = path.join(REMOTION_PUBLIC, 'veo');
  if (fs.existsSync(veoPublicDir)) {
    fs.rmSync(veoPublicDir, { recursive: true, force: true });
  }

  // Pre-create veo.json fixtures with safe prompts so Veo's RAI content
  // filter doesn't reject Claude-generated prompts during the test.
  for (const section of ['animation_section', 'veo_section']) {
    const sectionSpecDir = path.join(SPECS_DIR, section);
    fs.mkdirSync(sectionSpecDir, { recursive: true });
    fs.writeFileSync(
      path.join(sectionSpecDir, 'veo.json'),
      JSON.stringify({
        prompt:
          'A calm ocean wave rolling onto a sandy beach at sunset with golden light reflecting off the water, cinematic slow motion, 4K quality, aerial drone perspective',
      }),
    );
  }

  // NOTE: Remotion test compositions, bundle rebuild, and section
  // pre-rendering are now done INSIDE the test (after Stage 8) so that
  // real audio (from TTS) and real Veo clips are included in the bundle.
  console.log('[integration-setup] Setup complete. Remotion rebuild deferred to test.');
}
