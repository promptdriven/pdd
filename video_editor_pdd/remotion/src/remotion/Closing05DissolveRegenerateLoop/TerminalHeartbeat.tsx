import React from 'react';
import { useCurrentFrame } from 'remotion';
import {
  TERMINAL_X,
  TERMINAL_Y,
  TERMINAL_FONT_SIZE,
  TERMINAL_COLOR,
  TERMINAL_OPACITY,
  TERMINAL_CHECK_FRAMES,
  CYCLES,
} from './constants';

export const TerminalHeartbeat: React.FC = () => {
  const frame = useCurrentFrame();

  // Determine which text to show based on cycle timing
  // Before first dissolve starts: idle
  // During dissolve: "pdd generate"
  // After regenerate starts (check frame): "pdd generate → ✓"
  // Between cycles: show last completed state

  let text = 'pdd generate';

  // Check if we're past any check frames to show ✓
  const lastCheckIdx = TERMINAL_CHECK_FRAMES.reduce(
    (acc, checkFrame, idx) => (frame >= checkFrame ? idx : acc),
    -1
  );

  // Determine if we're in a dissolve phase (show "pdd generate")
  const inDissolve = CYCLES.some((cycle) => {
    const dissolveStart = cycle.startFrame;
    const dissolveEnd = dissolveStart + cycle.dissolveFrames;
    return frame >= dissolveStart && frame < dissolveEnd;
  });

  // Determine if we're in a regenerate phase or past a check (show "✓")
  const inRegenerate = CYCLES.some((cycle, idx) => {
    const regenStart = cycle.startFrame + cycle.dissolveFrames;
    const regenEnd = regenStart + cycle.regenerateFrames;
    return frame >= regenStart && frame < regenEnd;
  });

  if (frame < CYCLES[0].startFrame) {
    // Before any cycles, show command
    text = 'pdd generate';
  } else if (inDissolve) {
    text = 'pdd generate';
  } else if (inRegenerate || lastCheckIdx >= 0) {
    text = 'pdd generate → ✓';
  }

  // After all cycles complete, hold last state
  if (frame >= 160) {
    text = 'pdd generate → ✓';
  }

  return (
    <div
      style={{
        position: 'absolute',
        left: TERMINAL_X,
        top: TERMINAL_Y,
        fontFamily: 'JetBrains Mono, monospace',
        fontSize: TERMINAL_FONT_SIZE,
        color: TERMINAL_COLOR,
        opacity: TERMINAL_OPACITY,
        whiteSpace: 'nowrap',
        letterSpacing: 0.5,
      }}
    >
      {text}
    </div>
  );
};
