import fs from 'fs';
import path from 'path';

import { createSseStream } from '@/lib/sse';
import { loadProject } from '@/lib/project';
import { generateVeoClip, extractLastFrame, generateReferenceImage } from '@/lib/veo';
import { registerExecutor, runPipelineStage, createJob, runJob } from '@/lib/jobs';
import type { SseSend } from '@/lib/types';

/**
 * API ROUTE: app/api/pipeline/veo/run/route.ts
 */

export const runtime = 'nodejs';

/** Resolve a Veo prompt from specs on disk */
function resolveVeoPrompt(sectionId: string): string {
  const cwd = process.cwd();

  const candidates = [
    path.join(cwd, 'specs', sectionId, 'veo.json'),
    path.join(cwd, 'specs', sectionId, 'spec.json'),
    path.join(cwd, 'specs', sectionId, 'veo.txt'),
  ];

  for (const file of candidates) {
    if (!fs.existsSync(file)) continue;

    const raw = fs.readFileSync(file, 'utf-8').trim();
    if (!raw) continue;

    if (file.endsWith('.txt')) return raw;

    try {
      const json = JSON.parse(raw);
      if (typeof json.prompt === 'string') return json.prompt;
      if (typeof json.veoPrompt === 'string') return json.veoPrompt;
      if (typeof json.videoPrompt === 'string') return json.videoPrompt;
    } catch {
      // fall through
    }
  }

  throw new Error(
    `No Veo prompt found for section "${sectionId}". Checked: ${candidates.join(
      ', '
    )}`
  );
}

/** Ensure output directory exists */
function ensureDir(filePath: string): void {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

// Register the Veo executor once at module load
registerExecutor('veo', (params, send: SseSend) => {
  return async (onLog) => {
    const config = loadProject();
    const sections = config.sections;

    const requestedClips = Array.isArray(params.clips)
      ? new Set(params.clips.map(String))
      : null;

    const ordered = sections.filter(
      (s) => !requestedClips || requestedClips.has(s.id)
    );

    const total = ordered.length;
    const progressFn = (onLog as unknown as { progress?: (p: number) => void })
      .progress;

    let referenceImagePath: string | null = null;

    for (let i = 0; i < ordered.length; i++) {
      const section = ordered[i];
      const clipId = section.id;
      const aspectRatio = config.veo.defaultAspectRatio;

      const outputPath = path.join(
        process.cwd(),
        'outputs',
        'veo',
        `${clipId}.mp4`
      );
      const lastFramePath = path.join(
        process.cwd(),
        'outputs',
        'veo',
        `${clipId}_last_frame.png`
      );

      ensureDir(outputPath);

      try {
        send({ type: 'clip', clipId, status: 'generating' });

        const prompt = resolveVeoPrompt(section.id);
        onLog(`Generating Veo clip "${clipId}"`);
        onLog(`Prompt: ${prompt.substring(0, 120)}...`);

        await generateVeoClip(
          prompt,
          referenceImagePath,
          aspectRatio,
          outputPath
        );

        // Frame chaining for next clip
        if (i < ordered.length - 1) {
          onLog(`Extracting last frame for chaining: ${clipId}`);
          await extractLastFrame(outputPath, lastFramePath);
          referenceImagePath = lastFramePath;
        }

        send({ type: 'clip', clipId, status: 'done' });

        const percent = Math.round(((i + 1) / total) * 100);
        progressFn?.(percent);
      } catch (err) {
        const msg = err instanceof Error ? err.message : String(err);
        onLog(`Error generating clip "${clipId}": ${msg}`);
        send({ type: 'clip', clipId, status: 'error' });
        throw err;
      }
    }
  };
});

export async function POST(request: Request): Promise<Response> {
  const body = await request.json().catch(() => ({}));
  const { clips } = body ?? {};

  const { stream, send, done, error } = createSseStream();

  (async () => {
    try {
      const jobId = await runPipelineStage('veo', { clips }, send);
      send({ type: 'complete', jobId });
      done();
    } catch (err) {
      error(err instanceof Error ? err.message : 'Unknown error');
    }
  })();

  return new Response(stream, {
    headers: {
      'Content-Type': 'text/event-stream',
      'Cache-Control': 'no-cache',
      Connection: 'keep-alive',
    },
  });
}

/**
 * API ROUTE: app/api/pipeline/veo/clips/route.ts
 */

type VeoClip = {
  id: string;
  sectionId: string;
  aspectRatio: '16:9' | '9:16';
  status: 'done' | 'missing' | 'error';
  stale: boolean;
  frameChainDeps: string[];
};

function mtimeMs(filePath: string): number | null {
  try {
    return fs.statSync(filePath).mtimeMs;
  } catch {
    return null;
  }
}

export async function GET_clips(): Promise<Response> {
  const config = loadProject();
  const sections = config.sections;
  const aspectRatio = config.veo.defaultAspectRatio;

  const clips: VeoClip[] = sections.map((section, idx) => {
    const clipId = section.id;

    const clipPath = path.join(
      process.cwd(),
      'outputs',
      'veo',
      `${clipId}.mp4`
    );

    const prevSection = sections[idx - 1];
    const deps: string[] = prevSection
      ? [
          path.join(
            'outputs',
            'veo',
            `${prevSection.id}_last_frame.png`
          ),
        ]
      : [];

    const clipExists = fs.existsSync(clipPath);
    const status: VeoClip['status'] = clipExists ? 'done' : 'missing';

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

  return Response.json({ clips });
}

/**
 * API ROUTE: app/api/pipeline/veo/references/run/route.ts
 */

/** Resolve a reference prompt from disk */
function resolveReferencePrompt(referenceId: string): string {
  const cwd = process.cwd();

  const candidates = [
    path.join(cwd, 'specs', 'references.json'),
    path.join(cwd, 'specs', 'references', `${referenceId}.json`),
    path.join(cwd, 'specs', 'references', `${referenceId}.txt`),
  ];

  // references.json { [id]: {prompt} | string }
  if (fs.existsSync(candidates[0])) {
    const raw = fs.readFileSync(candidates[0], 'utf-8');
    const json = JSON.parse(raw);
    const value = json?.[referenceId];
    if (typeof value === 'string') return value;
    if (value && typeof value.prompt === 'string') return value.prompt;
  }

  for (const file of candidates.slice(1)) {
    if (!fs.existsSync(file)) continue;
    const raw = fs.readFileSync(file, 'utf-8').trim();
    if (!raw) continue;
    if (file.endsWith('.txt')) return raw;
    try {
      const json = JSON.parse(raw);
      if (typeof json.prompt === 'string') return json.prompt;
    } catch {
      // fall through
    }
  }

  return referenceId;
}

export async function POST_references(request: Request): Promise<Response> {
  const body = await request.json().catch(() => ({}));
  const { referenceId } = body ?? {};

  if (!referenceId || typeof referenceId !== 'string') {
    return Response.json(
      { error: 'referenceId is required' },
      { status: 400 }
    );
  }

  const jobId = createJob('veo', { referenceId, mode: 'reference' });

  (async () => {
    await runJob(jobId, async (onLog) => {
      const prompt = resolveReferencePrompt(referenceId);

      const outputPath = path.join(
        process.cwd(),
        'outputs',
        'veo',
        'references',
        `${referenceId}.png`
      );
      ensureDir(outputPath);

      onLog(`Generating reference image: ${referenceId}`);
      onLog(`Prompt: ${prompt.substring(0, 120)}...`);

      await generateReferenceImage(prompt, outputPath);
      onLog(`Reference image generated at ${outputPath}`);
    });
  })();

  return Response.json({ jobId });
}

/**
 * API ROUTE: app/api/pipeline/veo/staging-manifest/route.ts
 */

type AssetStagingEntry = {
  file: string;
  expected: boolean;
  present: boolean;
};

function listFilesRecursive(dir: string): string[] {
  if (!fs.existsSync(dir)) return [];
  const entries = fs.readdirSync(dir, { withFileTypes: true });

  const files: string[] = [];

  for (const entry of entries) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      files.push(...listFilesRecursive(full));
    } else if (entry.isFile()) {
      files.push(full);
    }
  }

  return files;
}

export async function GET_staging(): Promise<Response> {
  const config = loadProject();
  const sections = config.sections;

  const publicDir = path.join(process.cwd(), 'remotion', 'public');

  // Expected files
  const expectedFiles = sections.map((s) => `veo/${s.id}.mp4`);
  const expectedSet = new Set(expectedFiles);

  // Present files
  const presentFiles = listFilesRecursive(publicDir).map((absPath) =>
    absPath
      .replace(publicDir + path.sep, '')
      .replace(/\\/g, '/')
  );
  const presentSet = new Set(presentFiles);

  const entries: AssetStagingEntry[] = [];

  for (const file of expectedFiles) {
    entries.push({
      file,
      expected: true,
      present: presentSet.has(file),
    });
  }

  for (const file of presentFiles) {
    if (!expectedSet.has(file)) {
      entries.push({
        file,
        expected: false,
        present: true,
      });
    }
  }

  return Response.json({ files: entries });
}