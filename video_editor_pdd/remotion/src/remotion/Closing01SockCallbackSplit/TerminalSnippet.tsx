import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { TIMING, COLORS } from './constants';

export const TerminalSnippet: React.FC = () => {
  const frame = useCurrentFrame();

  const fullText = 'pdd bug → pdd fix → ✓';

  const charCount = Math.floor(
    interpolate(
      frame,
      [TIMING.TERMINAL_START, TIMING.TERMINAL_START + TIMING.TERMINAL_DURATION],
      [0, fullText.length],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.quad),
      }
    )
  );

  const displayText = fullText.slice(0, charCount);

  if (charCount === 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        right: 140,
        bottom: 60,
        fontFamily: '"JetBrains Mono", monospace',
        fontSize: 10,
        color: `rgba(74,144,217,0.7)`,
        zIndex: 10,
        whiteSpace: 'nowrap',
        textShadow: '0 0 6px rgba(0,0,0,0.9), 0 1px 4px rgba(0,0,0,0.8)',
      }}
    >
      {displayText}
      {charCount < fullText.length && (
        <span style={{ opacity: frame % 15 < 8 ? 1 : 0 }}>▊</span>
      )}
    </div>
  );
};
