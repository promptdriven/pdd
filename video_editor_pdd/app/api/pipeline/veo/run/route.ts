import fs from 'fs';
import path from 'path';

import { createSseStream } from '@/lib/sse';
import { loadProject } from '@/lib/project';
import { generateVeoClip, extractLastFrame } from '@/lib/veo';
import { registerExecutor, runPipelineStage } from '@/lib/jobs';
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

