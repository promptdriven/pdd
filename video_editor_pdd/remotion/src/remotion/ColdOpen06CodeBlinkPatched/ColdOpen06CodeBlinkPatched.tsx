import React from 'react';
import { AbsoluteFill } from 'remotion';
import {
  EDITOR_BG,
  GUTTER_BG,
  GUTTER_WIDTH,
  CANVAS_HEIGHT,
  CODE_LINES,
} from './constants';
import { CodeLineComponent } from './CodeLine';
import { PatchHighlights } from './PatchHighlight';
import { BlinkingCursor } from './BlinkingCursor';
import { ScanLine } from './ScanLine';

export const defaultColdOpen06CodeBlinkPatchedProps = {};

/**
 * Section 0.6: Code Blink — The Patched Function
 *
 * A full-screen code editor showing `processUserInput()`, 18+ lines,
 * visibly scarred with patch comments. A cursor blinks at line 1.
 * Patch scar highlights fade in sequentially. A subtle scan line
 * scrolls across to reinforce the screen feeling.
 *
 * Duration: 150 frames @ 30fps (5 seconds)
 */
export const ColdOpen06CodeBlinkPatched: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: EDITOR_BG,
        overflow: 'hidden',
      }}
    >
      {/* Gutter background */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: GUTTER_WIDTH,
          height: CANVAS_HEIGHT,
          backgroundColor: GUTTER_BG,
          borderRight: '1px solid #21262D',
        }}
      />

      {/* Patch scar highlights (behind code text) */}
      <PatchHighlights />

      {/* Code lines with syntax highlighting */}
      {CODE_LINES.map((line, idx) => (
        <CodeLineComponent key={idx} text={line} lineIndex={idx} />
      ))}

      {/* Blinking cursor at line 1, column 0 */}
      <BlinkingCursor />

      {/* Subtle scan line effect */}
      <ScanLine />
    </AbsoluteFill>
  );
};

export default ColdOpen06CodeBlinkPatched;
