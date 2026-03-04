/**
 * Tests for lib/clip-events.ts
 *
 * Verifies the globalThis-backed pub/sub used to bridge clip status events
 * from the Veo executor to the SSE stream endpoint.
 */

import { emitClipEvent, onClipEvent, type ClipEvent } from '@/lib/clip-events';

// Clean up listeners between tests to avoid cross-contamination
const _g = globalThis as typeof globalThis & {
  __clipEventListeners?: Set<unknown>;
};

beforeEach(() => {
  _g.__clipEventListeners?.clear();
});

// ---------------------------------------------------------------------------
// Source structure tests
// ---------------------------------------------------------------------------

describe('clip-events module exports', () => {
  it('exports emitClipEvent as a function', () => {
    expect(typeof emitClipEvent).toBe('function');
  });

  it('exports onClipEvent as a function', () => {
    expect(typeof onClipEvent).toBe('function');
  });
});

describe('globalThis persistence', () => {
  it('stores listeners on globalThis.__clipEventListeners', () => {
    expect(_g.__clipEventListeners).toBeInstanceOf(Set);
  });

  it('survives re-import (HMR resilience)', () => {
    const setRef = _g.__clipEventListeners;
    // Re-requiring the module should not create a new Set
    jest.isolateModules(() => {
      // eslint-disable-next-line @typescript-eslint/no-require-imports
      require('@/lib/clip-events');
    });
    expect(_g.__clipEventListeners).toBe(setRef);
  });
});

// ---------------------------------------------------------------------------
// Behavior tests
// ---------------------------------------------------------------------------

describe('emitClipEvent', () => {
  it('calls all registered listeners with the event data', () => {
    const received: ClipEvent[] = [];
    onClipEvent((evt) => received.push(evt));

    const event: ClipEvent = { clipId: 'intro', status: 'done' };
    emitClipEvent(event);

    expect(received).toEqual([event]);
  });

  it('delivers to multiple listeners', () => {
    const a: ClipEvent[] = [];
    const b: ClipEvent[] = [];
    onClipEvent((evt) => a.push(evt));
    onClipEvent((evt) => b.push(evt));

    const event: ClipEvent = { clipId: 'main', status: 'generating' };
    emitClipEvent(event);

    expect(a).toEqual([event]);
    expect(b).toEqual([event]);
  });

  it('does nothing when no listeners are registered', () => {
    // Should not throw
    expect(() => emitClipEvent({ clipId: 'x', status: 'error' })).not.toThrow();
  });
});

describe('onClipEvent', () => {
  it('returns an unsubscribe function', () => {
    const unsub = onClipEvent(() => {});
    expect(typeof unsub).toBe('function');
  });

  it('unsubscribed listener stops receiving events', () => {
    const received: ClipEvent[] = [];
    const unsub = onClipEvent((evt) => received.push(evt));

    emitClipEvent({ clipId: 'a', status: 'generating' });
    unsub();
    emitClipEvent({ clipId: 'b', status: 'done' });

    expect(received).toEqual([{ clipId: 'a', status: 'generating' }]);
  });

  it('other listeners still receive events after one unsubscribes', () => {
    const a: ClipEvent[] = [];
    const b: ClipEvent[] = [];
    const unsubA = onClipEvent((evt) => a.push(evt));
    onClipEvent((evt) => b.push(evt));

    unsubA();
    emitClipEvent({ clipId: 'outro', status: 'done' });

    expect(a).toEqual([]);
    expect(b).toEqual([{ clipId: 'outro', status: 'done' }]);
  });
});
