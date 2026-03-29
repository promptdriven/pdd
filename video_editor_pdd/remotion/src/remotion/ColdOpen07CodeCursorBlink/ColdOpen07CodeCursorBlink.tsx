import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { CodeLines } from './CodeLines';
import { BlinkingCursor } from './BlinkingCursor';

// ============================================================
// ColdOpen07CodeCursorBlink
//
// A dark-themed code editor showing a heavily-patched Python
// function (~40 lines). Patch comments and age-colored borders
// visualize accumulated technical debt. A block cursor blinks
// at line 23 inside the thicket of patched code.
//
// Duration: 48 frames @ 30fps (~1.6s)
// Animation: editor fades in over 10 frames, then holds with
// cursor blinking twice.
// ============================================================

const BACKGROUND_COLOR = '#1E1E2E';
const FADE_IN_FRAMES = 10;

export const defaultColdOpen07CodeCursorBlinkProps = {};

export const ColdOpen07CodeCursorBlink: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade-in: 0→1 over first 10 frames with easeOut(quad)
  const opacity = interpolate(frame, [0, FADE_IN_FRAMES], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        overflow: 'hidden',
      }}
    >
      <div
        style={{
          opacity,
          width: '100%',
          height: '100%',
          position: 'relative',
        }}
      >
        <CodeLines />
        <BlinkingCursor />
      </div>
    </AbsoluteFill>
  );
};

export default ColdOpen07CodeCursorBlink;
