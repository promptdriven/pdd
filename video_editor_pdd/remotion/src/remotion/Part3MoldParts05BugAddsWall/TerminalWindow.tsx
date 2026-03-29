import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  TERMINAL_X,
  TERMINAL_Y,
  TERMINAL_WIDTH,
  TERMINAL_HEIGHT,
  TERMINAL_BG,
  TERMINAL_BORDER,
  TERMINAL_TEXT,
  TERMINAL_PROMPT,
  TERMINAL_FADE_START,
} from './constants';

interface TerminalLine {
  text: string;
  showAtFrame: number;
  isCommand: boolean;
  color?: string;
}

const TERMINAL_LINES: TerminalLine[] = [
  { text: 'pdd bug user_parser', showAtFrame: 0, isCommand: true },
  { text: 'Creating failing test...', showAtFrame: 60, isCommand: false, color: TERMINAL_TEXT },
  { text: 'pdd fix user_parser', showAtFrame: 180, isCommand: true },
  { text: 'All tests passing ✓', showAtFrame: 270, isCommand: false, color: TERMINAL_TEXT },
];

/**
 * The terminal window in the bottom-right corner.
 * It appears at its own Sequence start frame (frame 30 in the parent).
 * `localFrame` here is relative to this component's mount.
 */
export const TerminalWindow: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in
  const fadeIn = interpolate(frame, [0, 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Subtle fade at the very end (relative frames from terminal mount,
  // terminal mounts at frame 30 in parent, so TERMINAL_FADE_START-30)
  const lateFade = interpolate(
    frame,
    [TERMINAL_FADE_START - 30, TERMINAL_FADE_START - 30 + 60],
    [1, 0.6],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  const opacity = fadeIn * lateFade;

  return (
    <div
      style={{
        position: 'absolute',
        left: TERMINAL_X,
        top: TERMINAL_Y,
        width: TERMINAL_WIDTH,
        height: TERMINAL_HEIGHT,
        backgroundColor: TERMINAL_BG,
        border: `1px solid ${TERMINAL_BORDER}`,
        borderRadius: 6,
        opacity,
        padding: '10px 14px',
        boxSizing: 'border-box',
        overflow: 'hidden',
        display: 'flex',
        flexDirection: 'column',
        gap: 6,
      }}
    >
      {/* Title bar */}
      <div
        style={{
          display: 'flex',
          gap: 6,
          marginBottom: 4,
        }}
      >
        <div style={{ width: 10, height: 10, borderRadius: '50%', backgroundColor: '#EF4444', opacity: 0.7 }} />
        <div style={{ width: 10, height: 10, borderRadius: '50%', backgroundColor: '#F59E0B', opacity: 0.7 }} />
        <div style={{ width: 10, height: 10, borderRadius: '50%', backgroundColor: '#22C55E', opacity: 0.7 }} />
      </div>

      {/* Terminal lines */}
      {TERMINAL_LINES.map((line, i) => {
        // Each line types in over 10 frames after its showAtFrame
        const lineOpacity = interpolate(
          frame,
          [line.showAtFrame, line.showAtFrame + 10],
          [0, 1],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        );

        if (lineOpacity <= 0) return null;

        return (
          <div
            key={i}
            style={{
              fontFamily: '"JetBrains Mono", monospace',
              fontSize: 12,
              lineHeight: '18px',
              opacity: lineOpacity,
              whiteSpace: 'nowrap',
            }}
          >
            {line.isCommand && (
              <span style={{ color: TERMINAL_PROMPT }}>$ </span>
            )}
            <span style={{ color: line.color || (line.isCommand ? '#E2E8F0' : TERMINAL_TEXT) }}>
              {line.text}
            </span>
          </div>
        );
      })}
    </div>
  );
};
