import fs from 'fs';
import path from 'path';

import { createSseStream } from '@/lib/sse';
import { loadProject } from '@/lib/project';
import { generateVeoClip, extractLastFrame } from '@/lib/veo';
import { registerExecutor, runPipelineStage } from '@/lib/jobs';
import { emitClipEvent } from '@/lib/clip-events';
import type { SseSend } from '@/lib/types';
import {
  generateDeterministicVeoClip,
  isDeterministicPipelineMode,
} from '@/lib/deterministic-pipeline';
import {
  listResolvedVeoClipSpecs,
  normalizeSpecDir,
  selectCanonicalVeoPromptSpec,
} from '@/lib/veo-spec-context';
import {
  resolveSectionHasVeoIntent,
  resolveSectionVeoPromptFromScript,
} from '@/app/api/pipeline/_lib/script-visual-intent';

/**
 * API ROUTE: app/api/pipeline/veo/run/route.ts
 */

export const runtime = 'nodejs';

/** Resolve a Veo prompt from specs on disk */
function resolveVeoPrompt(
  section: { id: string; label: string; specDir?: string | null },
  mainScriptContent: string | null
): string {
  const cwd = process.cwd();
  const normalizedSpecDir = normalizeSpecDir(section.specDir ?? section.id);

  // 1. Check JSON and text candidates first
  const candidates = [
    path.join(cwd, 'specs', normalizedSpecDir, 'veo.json'),
    path.join(cwd, 'specs', normalizedSpecDir, 'spec.json'),
    path.join(cwd, 'specs', normalizedSpecDir, 'veo.txt'),
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
  const specDir = path.join(cwd, 'specs', normalizedSpecDir);
  if (fs.existsSync(specDir)) {
    const markdownEntries = fs
      .readdirSync(specDir)
      .filter((file) => file.endsWith('.md') && !file.startsWith('AUDIT_'))
      .map((file) => ({
        path: path.posix.join('specs', normalizedSpecDir, file),
        content: fs.readFileSync(path.join(specDir, file), 'utf-8'),
      }));

    const canonicalSpec = selectCanonicalVeoPromptSpec(markdownEntries);
    if (canonicalSpec) return canonicalSpec.prompt;
  }

  // 3. Check narrative/main_script.md for this section's [veo:] marker
  if (mainScriptContent) {
    const prompt = resolveSectionVeoPromptFromScript(mainScriptContent, {
      id: section.id,
      label: section.label,
    });
    if (prompt) return prompt;
  }

  throw new Error(
    `No Veo prompt found for section "${section.id}". Checked JSON/txt candidates and markdown files in specs/${normalizedSpecDir}/.`
  );
}

/** Ensure output directory exists */
function ensureDir(filePath: string): void {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

type ResolvedClipJob = {
  id: string;
  sectionId: string;
  prompt: string;
};

function listSectionMarkdownEntries(
  section: { id: string; specDir?: string | null }
): { path: string; content: string }[] {
  const cwd = process.cwd();
  const normalizedSpecDir = normalizeSpecDir(section.specDir ?? section.id);
  const specDir = path.join(cwd, 'specs', normalizedSpecDir);

  if (!fs.existsSync(specDir)) {
    return [];
  }

  return fs
    .readdirSync(specDir)
    .filter((file) => file.endsWith('.md') && !file.startsWith('AUDIT_'))
    .map((file) => ({
      path: path.posix.join('specs', normalizedSpecDir, file),
      content: fs.readFileSync(path.join(specDir, file), 'utf-8'),
    }));
}

function resolveSectionClipJobs(
  section: { id: string; label: string; specDir?: string | null },
  mainScriptContent: string | null
): ResolvedClipJob[] {
  const markdownEntries = listSectionMarkdownEntries(section);
  const resolvedSpecs = listResolvedVeoClipSpecs(markdownEntries);
  if (resolvedSpecs.length > 0) {
    return resolvedSpecs.map((clip) => ({
      id: clip.id,
      sectionId: section.id,
      prompt: clip.prompt,
    }));
  }

  return [
    {
      id: section.id,
      sectionId: section.id,
      prompt: resolveVeoPrompt(section, mainScriptContent),
    },
  ];
}

// Register the Veo executor once at module load
registerExecutor('veo', (params, send: SseSend) => {
  return async (onLog) => {
    const config = loadProject();
    const sections = config.sections;
    const mainScriptPath = path.join(process.cwd(), 'narrative', 'main_script.md');
    let mainScriptContent: string | null = null;

    if (fs.existsSync(mainScriptPath)) {
      try {
        mainScriptContent = fs.readFileSync(mainScriptPath, 'utf-8');
      } catch {
        mainScriptContent = null;
      }
    }

    const requestedClips = Array.isArray(params.clips)
      ? new Set(params.clips.map(String))
      : null;

    const orderedSections = sections.filter((s) =>
      mainScriptContent
        ? resolveSectionHasVeoIntent(mainScriptContent, {
            id: s.id,
            label: s.label,
          }) !== false
        : true
    );

    const ordered = orderedSections.flatMap((section) =>
      resolveSectionClipJobs(section, mainScriptContent)
    ).filter(
      (clip) =>
        !requestedClips ||
        requestedClips.has(clip.id) ||
        requestedClips.has(clip.sectionId)
    );

    const total = ordered.length;
    const progressFn = (onLog as unknown as { progress?: (p: number) => void })
      .progress;

    let referenceImagePath: string | null = null;

    for (let i = 0; i < ordered.length; i++) {
      const clip = ordered[i];
      const clipId = clip.id;
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

        const prompt = clip.prompt;
        onLog(`Generating Veo clip "${clipId}" for section "${clip.sectionId}"`);
        onLog(`Prompt: ${prompt.substring(0, 120)}...`);

        if (isDeterministicPipelineMode()) {
          generateDeterministicVeoClip(outputPath, onLog);
        } else {
          await generateVeoClip(
            prompt,
            referenceImagePath,
            aspectRatio,
            outputPath
          );
        }

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
