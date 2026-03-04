/**
 * Lightweight pub/sub for clip status events.
 *
 * Bridges clip events from the Veo executor (POST /api/pipeline/veo/run)
 * to the SSE stream endpoint (GET /api/pipeline/veo/stream) so the
 * frontend EventSource receives real-time clip status updates.
 *
 * Uses globalThis to survive Next.js dev-mode HMR, matching the pattern
 * established in lib/db.ts and lib/jobs.ts.
 */

export interface ClipEvent {
  clipId: string;
  status: 'generating' | 'done' | 'error';
}

export type ClipEventListener = (event: ClipEvent) => void;

const _g = globalThis as typeof globalThis & {
  __clipEventListeners?: Set<ClipEventListener>;
};

if (!_g.__clipEventListeners) {
  _g.__clipEventListeners = new Set();
}

const listeners: Set<ClipEventListener> = _g.__clipEventListeners;

/** Broadcast a clip event to all connected listeners. */
export function emitClipEvent(event: ClipEvent): void {
  for (const listener of listeners) {
    listener(event);
  }
}

/**
 * Subscribe to clip events. Returns an unsubscribe function.
 */
export function onClipEvent(listener: ClipEventListener): () => void {
  listeners.add(listener);
  return () => {
    listeners.delete(listener);
  };
}
