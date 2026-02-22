/**
 * Example: How to use the next.config.ts configuration module
 *
 * This file demonstrates how the Next.js 15 configuration works in practice.
 * The config itself (next.config.ts) is placed at the project root and is
 * automatically read by Next.js — you never import it directly in application
 * code. Instead, this example shows the three features it enables and how
 * your application code interacts with each one.
 *
 * ─────────────────────────────────────────────────────────────────────────────
 * Feature 1: serverExternalPackages — better-sqlite3 in Route Handlers
 * ─────────────────────────────────────────────────────────────────────────────
 * Because `serverExternalPackages: ['better-sqlite3']` is set, the native
 * .node addon is excluded from webpack bundling and loaded at runtime.
 * This means you can use better-sqlite3 in any server-side module:
 *
 *   // app/api/data/route.ts
 *   import Database from 'better-sqlite3';
 *
 *   const db = new Database('pipeline.db');
 *
 *   export async function GET() {
 *     const rows = db.prepare('SELECT * FROM jobs').all();
 *     return Response.json(rows);
 *   }
 *
 * Without `serverExternalPackages`, Next.js would try to bundle the native
 * module and fail at build time.
 *
 * ─────────────────────────────────────────────────────────────────────────────
 * Feature 2: Server Actions with 10 MB body size limit
 * ─────────────────────────────────────────────────────────────────────────────
 * The `experimental.serverActions.bodySizeLimit: '10mb'` setting allows
 * Server Actions to accept payloads up to 10 MB (default is 1 MB).
 *
 *   // app/actions/upload.ts
 *   'use server';
 *
 *   export async function uploadVideo(formData: FormData) {
 *     const file = formData.get('video') as File;       // up to 10 MB
 *     const buffer = Buffer.from(await file.arrayBuffer());
 *     // ... save buffer to disk or database
 *     return { success: true, size: buffer.length };
 *   }
 *
 *   // app/upload/page.tsx (client component)
 *   'use client';
 *   import { uploadVideo } from '../actions/upload';
 *
 *   export default function UploadPage() {
 *     return (
 *       <form action={uploadVideo}>
 *         <input type="file" name="video" accept="video/*" />
 *         <button type="submit">Upload</button>
 *       </form>
 *     );
 *   }
 *
 * ─────────────────────────────────────────────────────────────────────────────
 * Feature 3: SSE streaming headers for /api/pipeline/* and /api/jobs/*
 * ─────────────────────────────────────────────────────────────────────────────
 * The `headers()` function in next.config.ts automatically attaches
 * `Cache-Control: no-cache, no-transform` and `X-Accel-Buffering: no`
 * to any response from these routes. This prevents nginx (or other reverse
 * proxies) from buffering Server-Sent Events.
 */

// ============================================================================
// Example 1: SSE Route Handler — app/api/pipeline/status/route.ts
// ============================================================================
// This is what a streaming SSE endpoint looks like. The headers from
// next.config.ts are applied automatically by Next.js on top of any
// headers you set here.

export async function GET_pipeline_status(): Promise<Response> {
  const encoder = new TextEncoder();

  let intervalId: ReturnType<typeof setInterval> | null = null;
  const stream = new ReadableStream({
    start(controller) {
      let count = 0;
      intervalId = setInterval(() => {
        count++;
        const event = `data: ${JSON.stringify({
          stage: 'rendering',
          progress: count * 10,
          timestamp: new Date().toISOString(),
        })}\n\n`;

        controller.enqueue(encoder.encode(event));

        if (count >= 10) {
          clearInterval(intervalId!);
          intervalId = null;
          controller.enqueue(encoder.encode('data: [DONE]\n\n'));
          controller.close();
        }
      }, 500);
    },
    cancel() {
      if (intervalId !== null) {
        clearInterval(intervalId);
        intervalId = null;
      }
    },
  });

  // These headers are set by the Route Handler; next.config.ts adds
  // Cache-Control and X-Accel-Buffering on top automatically.
  return new Response(stream, {
    headers: {
      'Content-Type': 'text/event-stream',
      Connection: 'keep-alive',
    },
  });
}

// ============================================================================
// Example 2: SSE Route Handler — app/api/jobs/stream/route.ts
// ============================================================================

interface Job {
  id: string;
  status: 'queued' | 'running' | 'complete' | 'failed';
  name: string;
}

export async function GET_jobs_stream(): Promise<Response> {
  const encoder = new TextEncoder();

  const jobs: Job[] = [
    { id: '1', status: 'queued', name: 'Transcode 4K' },
    { id: '2', status: 'running', name: 'Color Grade' },
    { id: '3', status: 'complete', name: 'Audio Mix' },
  ];

  const stream = new ReadableStream({
    start(controller) {
      let index = 0;
      const interval = setInterval(() => {
        if (index >= jobs.length) {
          clearInterval(interval);
          controller.close();
          return;
        }
        const event = `event: job-update\ndata: ${JSON.stringify(jobs[index])}\n\n`;
        controller.enqueue(encoder.encode(event));
        index++;
      }, 1000);
    },
  });

  return new Response(stream, {
    headers: {
      'Content-Type': 'text/event-stream',
      Connection: 'keep-alive',
    },
  });
}

// ============================================================================
// Example 3: Client-side SSE consumer
// ============================================================================
// This would live in a client component, e.g. app/dashboard/page.tsx

/**
 * Connects to an SSE endpoint and invokes a callback for each event.
 *
 * @param url - The SSE endpoint URL, e.g. '/api/pipeline/status'
 * @param onMessage - Callback invoked with each parsed event data string.
 *                    Receives the raw `data` field from the SSE message.
 * @returns An EventSource instance. Call `.close()` to disconnect.
 *
 * @example
 * ```ts
 * const source = connectSSE('/api/jobs/stream', (data) => {
 *   const job = JSON.parse(data);
 *   console.log(`Job ${job.id}: ${job.status}`);
 * });
 *
 * // Later, to disconnect:
 * source.close();
 * ```
 */
export function connectSSE(
  url: string,
  onMessage: (data: string) => void,
): EventSource {
  const source = new EventSource(url);

  source.onmessage = (event: MessageEvent) => {
    onMessage(event.data);
  };

  source.onerror = (err) => {
    console.error('SSE connection error:', err);
    source.close();
  };

  return source;
}

// ============================================================================
// Example 4: Verifying the config shape (useful in tests or CI)
// ============================================================================

/**
 * Validates that a Next.js config object has the expected structure
 * for the video pipeline project.
 *
 * @param config - The NextConfig object to validate.
 * @returns An object with `valid: boolean` and `errors: string[]`.
 *
 * @example
 * ```ts
 * import nextConfig from './next.config';  // only works at project root
 * const result = validatePipelineConfig(nextConfig);
 * console.log(result);
 * // { valid: true, errors: [] }
 * ```
 */
export function validatePipelineConfig(config: Record<string, unknown>): {
  valid: boolean;
  errors: string[];
} {
  const errors: string[] = [];

  // Check serverExternalPackages
  const sep = config.serverExternalPackages;
  if (!Array.isArray(sep) || !sep.includes('better-sqlite3')) {
    errors.push(
      "serverExternalPackages must include 'better-sqlite3' for native module support",
    );
  }

  // Check body size limit
  const experimental = config.experimental as Record<string, unknown> | undefined;
  const serverActions = experimental?.serverActions as Record<string, unknown> | undefined;
  if (serverActions?.bodySizeLimit !== '10mb') {
    errors.push(
      "experimental.serverActions.bodySizeLimit must be '10mb' for large uploads",
    );
  }

  // Check headers function exists
  if (typeof config.headers !== 'function') {
    errors.push('headers() async function is required for SSE proxy headers');
  }

  return { valid: errors.length === 0, errors };
}

// ============================================================================
// Self-test: run this file directly with ts-node / tsx to verify
// ============================================================================

async function main() {
  console.log('=== next.config.ts Usage Examples ===\n');

  // 1. Validate config shape
  const mockConfig = {
    serverExternalPackages: ['better-sqlite3'],
    experimental: {
      serverActions: {
        bodySizeLimit: '10mb',
      },
    },
    headers: async () => [
      { 
        source: '/api/pipeline/:path*',
        headers: [
          { key: 'Cache-Control', value: 'no-cache, no-transform' },
          { key: 'X-Accel-Buffering', value: 'no' },
        ],
      },
      { 
        source: '/api/jobs/:path*',
        headers: [
          { key: 'Cache-Control', value: 'no-cache, no-transform' },
          { key: 'X-Accel-Buffering', value: 'no' },
        ],
      },
    ],
  };

  const validation = validatePipelineConfig(mockConfig);
  console.log('Config validation:', validation);
  // Output: { valid: true, errors: [] }

  // 2. Show what headers() returns
  const headersFn = mockConfig.headers;
  const headerRules = await headersFn();
  console.log('\nSSE header rules:');
  for (const rule of headerRules) {
    console.log(`  Route: ${rule.source}`);
    for (const h of rule.headers) {
      console.log(`    ${h.key}: ${h.value}`);
    }
  }

  // 3. Demonstrate SSE stream creation (server-side)
  console.log('\nCreating mock SSE stream (pipeline status)...');
  const response = await GET_pipeline_status();
  console.log('Response Content-Type:', response.headers.get('Content-Type'));
  console.log('Response has ReadableStream body:', response.body !== null);

  // Read first few chunks
  const reader = response.body!.getReader();
  const decoder = new TextDecoder();
  let chunks = 0;
  while (chunks < 3) {
    const { done, value } = await reader.read();
    if (done) break;
    console.log('  Chunk:', decoder.decode(value).trim());
    chunks++;
  }
  reader.cancel();

  console.log('\n=== All examples completed successfully ===');
}

if (require.main === module) {
  main().catch(console.error);
}