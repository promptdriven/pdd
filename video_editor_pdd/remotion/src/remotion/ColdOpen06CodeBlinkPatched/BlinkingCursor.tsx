import React from 'react';
import { useCurrentFrame } from 'remotion';
import {
  CURSOR_COLOR,
  CURSOR_WIDTH,
  CURSOR_HEIGHT,
  CODE_X_START,
  CODE_Y_START,
  CODE_LINE_HEIGHT,
  CURSOR_ON_MS,
  CURSOR_OFF_MS,
  FPS,
  DELIBERATE_BLINK_START_FRAME,
  TOTAL_FRAMES,
} from './constants';

/**
 * A blinking cursor positioned at line 1, column 0.
 *
 * Normal blink: 530ms on / 530ms off.
 * After frame 120: two deliberate blinks, with the final one held longer (800ms).
 */
export const BlinkingCursor: React.FC = () => {
  const frame = useCurrentFrame();

  const cycleMs = CURSOR_ON_MS + CURSOR_OFF_MS; // 1060ms
  const currentTimeMs = (frame / FPS) * 1000;

  let visible: boolean;

  if (frame >= DELIBERATE_BLINK_START_FRAME) {
    // Deliberate blink section (frames 120-150, 1 second)
    // Two deliberate blinks, final one held longer
    const deliberateTimeMs =
      ((frame - DELIBERATE_BLINK_START_FRAME) / FPS) * 1000;
    const totalDeliberateMs =
      ((TOTAL_FRAMES - DELIBERATE_BLINK_START_FRAME) / FPS) * 1000; // 1000ms

    // Blink 1: off 0-200ms, on 200-530ms
    // Blink 2: off 530-600ms, on 600-1000ms (held for 800ms — the long pause)
    if (deliberateTimeMs < 200) {
      visible = false;
    } else if (deliberateTimeMs < 530) {
      visible = true;
    } else if (deliberateTimeMs < 600) {
      visible = false;
    } else if (deliberateTimeMs < totalDeliberateMs) {
      // Final long hold — 400ms visible
      visible = true;
    } else {
      visible = true;
    }
  } else {
    // Normal blink cycle
    const posInCycle = currentTimeMs % cycleMs;
    visible = posInCycle < CURSOR_ON_MS;
  }

  const x = CODE_X_START;
  const y = CODE_Y_START + (CODE_LINE_HEIGHT - CURSOR_HEIGHT) / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width: CURSOR_WIDTH,
        height: CURSOR_HEIGHT,
        backgroundColor: CURSOR_COLOR,
        opacity: visible ? 1 : 0,
      }}
    />
  );
};
