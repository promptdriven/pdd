import fs from 'fs';
import path from 'path';
import { NextResponse } from "next/server";

import { createSseStream } from '@/lib/sse';
import { loadProject } from '@/lib/project';
import { generateReferenceImage } from '@/lib/veo';
import { getProjectDir } from "@/lib/projects";

/**
 * API ROUTE: app/api/pipeline/veo/references/run/route.ts
 *
 * Triggers regeneration of a character reference image.
 * Body: { referenceId: string }
 *
 * Runs inline (no job system / DAG) because reference generation is a
 * single Imagen API call, not a multi-step pipeline stage.
 */

export async function POST(request: Request): Promise<Response> {
  const body = await request.json().catch(() => ({}));
  const { referenceId } = body ?? {};

  if (!referenceId || typeof referenceId !== "string") {
    return NextResponse.json(
      { error: "referenceId is required" },
      { status: 400 }
    );
  }

  const { stream, send, done, error } = createSseStream();
  const jobId = `ref-${referenceId}-${Date.now()}`;

  (async () => {
    try {
      send({ type: 'started', jobId });

      const config = loadProject();
      const references = config.veo?.references ?? [];
      const ref = references.find((r: { id: string }) => r.id === referenceId);

      const label = ref?.label ?? referenceId;
      const prompt = `Professional portrait photograph of ${label}, detailed face, neutral background`;

      const outputPath = path.join(
        getProjectDir(),
        'outputs',
        'veo',
        'references',
        `${referenceId}.png`
      );

      fs.mkdirSync(path.dirname(outputPath), { recursive: true });

      send({ type: 'log', message: `Generating reference portrait for "${label}"`, jobId });
      send({ type: 'log', message: `Prompt: ${prompt}`, jobId });

      await generateReferenceImage(prompt, outputPath);

      send({ type: 'log', message: `Reference portrait saved: ${referenceId}.png`, jobId });
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
