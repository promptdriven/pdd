import fs from 'fs';
import path from 'path';

import { createSseStream } from '@/lib/sse';
import { loadProject } from '@/lib/project';
import { generateVeoClip, extractLastFrame } from '@/lib/veo';
import { registerExecutor, runPipelineStage } from '@/lib/jobs';
import { emitClipEvent } from '@/lib/clip-events';
import type { SseSend } from '@/lib/types';

/**
 * API ROUTE: app/api/pipeline/veo/run/route.ts
 */

export const runtime = 'nodejs';

/**
 * Extract a Veo prompt from a [veo: ...] marker inside markdown content.
 * Returns null if no marker is found.
 */
function extractVeoMarker(content: string): string | null {
  const match = content.match(/\[veo:\s*(.+?)\]/i);
  return match ? match[1].trim() : null;
}

/** Resolve a Veo prompt from specs on disk */
function resolveVeoPrompt(sectionId: string): string {
  const cwd = process.cwd();

  // 1. Check JSON and text candidates first
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

  // 2. Scan markdown files in specs/{sectionId}/ for [veo: ...] markers
  const specDir = path.join(cwd, 'specs', sectionId);
  if (fs.existsSync(specDir)) {
    const mdFiles = fs
      .readdirSync(specDir)
      .filter((f) => f.endsWith('.md'))
      .sort();

    for (const mdFile of mdFiles) {
      const content = fs.readFileSync(path.join(specDir, mdFile), 'utf-8');
      const prompt = extractVeoMarker(content);
      if (prompt) return prompt;
    }
  }

  // 3. Check narrative/main_script.md for this section's [veo:] marker
  const mainScript = path.join(cwd, 'narrative', 'main_script.md');
  if (fs.existsSync(mainScript)) {
    const content = fs.readFileSync(mainScript, 'utf-8');
    // Find the section in the script and look for [veo:] marker within it
    const sectionPattern = new RegExp(
      `##\\s+.*${sectionId.replace(/_/g, '[\\s_]')}.*?\\n([\\s\\S]*?)(?=\\n##\\s|$)`,
      'i'
    );
    const sectionMatch = content.match(sectionPattern);
    if (sectionMatch) {
      const prompt = extractVeoMarker(sectionMatch[1]);
      if (prompt) return prompt;
    }
    // Also try the whole file as a last resort
    const prompt = extractVeoMarker(content);
    if (prompt) return prompt;
  }

  throw new Error(
    `No Veo prompt found for section "${sectionId}". Checked JSON/txt candidates and markdown files in specs/${sectionId}/.`
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
        emitClipEvent({ clipId, status: 'generating', message: 'Generating…' });

        const prompt = resolveVeoPrompt(section.specDir ?? section.id);
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
        emitClipEvent({ clipId, status: 'done', message: 'Done' });

        const percent = Math.round(((i + 1) / total) * 100);
        progressFn?.(percent);
      } catch (err) {
        const msg = err instanceof Error ? err.message : String(err);
        onLog(`Error generating clip "${clipId}": ${msg}`);
        send({ type: 'clip', clipId, status: 'error' });
        emitClipEvent({ clipId, status: 'error', message: msg });
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

