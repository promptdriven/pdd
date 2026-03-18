// TerminalHeartbeat.tsx — Corner terminal cycling "pdd generate -> checkmark"
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { TERMINAL, CYCLES } from './constants';

export const TerminalHeartbeat: React.FC = () => {
  const frame = useCurrentFrame();

  // Determine terminal text based on current frame within cycles
  // Between dissolve start and regenerate start: show "pdd generate"
  // After regenerate start: show "pdd generate -> checkmark"
  let text = `${TERMINAL.command}`;

  for (const cycle of CYCLES) {
    if (frame >= cycle.dissolveStart && frame < cycle.regenerateStart) {
      text = `$ ${TERMINAL.command}`;
      break;
    }
    if (
      frame >= cycle.regenerateStart &&
      frame < cycle.regenerateStart + cycle.regenerateDuration
    ) {
      text = `$ ${TERMINAL.command} \u2192 ${TERMINAL.successMark}`;
      break;
    }
    // After all cycles in hold phase, show final success
    if (frame >= 160) {
      text = `$ ${TERMINAL.command} \u2192 ${TERMINAL.successMark}`;
    }
  }

  // Blinking cursor
  const showCursor = Math.floor(frame / 15) % 2 === 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: TERMINAL.x,
        top: TERMINAL.y,
        fontFamily: 'JetBrains Mono, monospace',
        fontSize: TERMINAL.fontSize,
        color: TERMINAL.color,
        opacity: TERMINAL.opacity,
        whiteSpace: 'nowrap',
        letterSpacing: 0.5,
      }}
    >
      {text}
      <span style={{ opacity: showCursor ? 1 : 0 }}>{'\u2588'}</span>
    </div>
  );
};
