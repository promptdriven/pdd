import fs from 'fs';
import path from 'path';

const PROJECT_ROOT = path.resolve(__dirname, '..', '..', '..');

const PROJECT_JSON = path.join(PROJECT_ROOT, 'project.json');
const MAIN_SCRIPT = path.join(PROJECT_ROOT, 'narrative', 'main_script.md');
const PIPELINE_DB = path.join(PROJECT_ROOT, 'pipeline.db');
const SPECS_DIR = path.join(PROJECT_ROOT, 'specs');
const SPECS_BACKUP = SPECS_DIR + '.integration-backup';

const REMOTION_DIR = path.join(PROJECT_ROOT, 'remotion');
const REMOTION_SRC = path.join(REMOTION_DIR, 'src', 'remotion');
const REMOTION_PUBLIC = path.join(REMOTION_DIR, 'public');
const REMOTION_BUILD = path.join(REMOTION_DIR, 'build');
const REMOTION_BUILD_BACKUP = REMOTION_BUILD + '.integration-backup';
const ROOT_TSX = path.join(REMOTION_SRC, 'Root.tsx');

const BACKUP_SUFFIX = '.integration-backup';
const REMOTION_SNAPSHOT = path.join(PROJECT_ROOT, '.integration-remotion-snapshot.json');
const PUBLIC_SNAPSHOT = path.join(PROJECT_ROOT, '.integration-remotion-public-snapshot.json');

function restoreIfBackupExists(filePath: string): void {
  const backup = filePath + BACKUP_SUFFIX;
  if (fs.existsSync(backup)) {
    fs.copyFileSync(backup, filePath);
    fs.unlinkSync(backup);
  } else if (fs.existsSync(filePath)) {
    // No backup means the file didn't exist before — remove the test artifact
    fs.unlinkSync(filePath);
  }
}

/** Remove files/dirs that were created during the test (not in the snapshot). */
function cleanBySnapshot(dir: string, snapshotFile: string): void {
  if (!fs.existsSync(snapshotFile)) return;
  try {
    const original: string[] = JSON.parse(fs.readFileSync(snapshotFile, 'utf-8'));
    const originalSet = new Set(original);
    if (fs.existsSync(dir)) {
      for (const entry of fs.readdirSync(dir)) {
        if (!originalSet.has(entry)) {
          const fullPath = path.join(dir, entry);
          const stat = fs.statSync(fullPath);
          if (stat.isDirectory()) {
            fs.rmSync(fullPath, { recursive: true, force: true });
          } else {
            fs.unlinkSync(fullPath);
          }
        }
      }
    }
    fs.unlinkSync(snapshotFile);
  } catch {
    // Best effort cleanup
  }
}

export default function globalTeardown(): void {
  restoreIfBackupExists(PROJECT_JSON);
  restoreIfBackupExists(MAIN_SCRIPT);

  // Restore pipeline.db and its WAL files
  for (const suffix of ['', '-wal', '-shm']) {
    restoreIfBackupExists(PIPELINE_DB + suffix);
  }

  // Restore specs directory
  if (fs.existsSync(SPECS_DIR)) {
    fs.rmSync(SPECS_DIR, { recursive: true, force: true });
  }
  if (fs.existsSync(SPECS_BACKUP)) {
    fs.renameSync(SPECS_BACKUP, SPECS_DIR);
  }

  // Clean up generated composition files in remotion/src/remotion/
  cleanBySnapshot(REMOTION_SRC, REMOTION_SNAPSHOT);

  // Clean up audio/veo files added to remotion/public/ during the test
  cleanBySnapshot(REMOTION_PUBLIC, PUBLIC_SNAPSHOT);

  // Restore Remotion Root.tsx
  restoreIfBackupExists(ROOT_TSX);

  // Restore Remotion build directory
  if (fs.existsSync(REMOTION_BUILD)) {
    fs.rmSync(REMOTION_BUILD, { recursive: true, force: true });
  }
  if (fs.existsSync(REMOTION_BUILD_BACKUP)) {
    fs.renameSync(REMOTION_BUILD_BACKUP, REMOTION_BUILD);
  }
}
