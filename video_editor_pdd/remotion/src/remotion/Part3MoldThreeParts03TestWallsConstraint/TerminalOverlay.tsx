import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  TERMINAL_LINES,
  TERMINAL_BG,
  TERMINAL_BORDER,
  TERMINAL_TEXT,
  MONO_FONT,
} from './constants';

const TerminalOverlay: React.FC = () => {
  const frame = useCurrentFrame();

  // Terminal appears at frame 150 relative to parent Sequence
  // This component is mounted inside a <Sequence from={150}>
  // so frame 0 here = frame 150 in the parent.

  // Slide up entrance
  const enterY = interpolate(frame, [0, 15], [20, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  const enterOpacity = interpolate(frame, [0, 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <div
      style={{
        position: 'absolute',
        right: 80,
        bottom: 60,
        width: 340,
        height: 150,
        backgroundColor: TERMINAL_BG,
        border: `1px solid ${TERMINAL_BORDER}`,
        borderRadius: 6,
        padding: '10px 14px',
        transform: `translateY(${enterY}px)`,
        opacity: enterOpacity,
        overflow: 'hidden',
        display: 'flex',
        flexDirection: 'column',
        gap: 3,
      }}
    >
      {/* Title bar dots */}
      <div style={{ display: 'flex', gap: 5, marginBottom: 6 }}>
        <div
          style={{
            width: 7,
            height: 7,
            borderRadius: '50%',
            backgroundColor: '#EF4444',
            opacity: 0.6,
          }}
        />
        <div
          style={{
            width: 7,
            height: 7,
            borderRadius: '50%',
            backgroundColor: '#F59E0B',
            opacity: 0.6,
          }}
        />
        <div
          style={{
            width: 7,
            height: 7,
            borderRadius: '50%',
            backgroundColor: '#22C55E',
            opacity: 0.6,
          }}
        />
      </div>

      {/* Terminal lines */}
      {TERMINAL_LINES.map((line, i) => {
        const lineFrame = frame - line.delay;
        if (lineFrame < 0) return null;

        const lineOpacity = interpolate(lineFrame, [0, 8], [0, 1], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        });

        return (
          <div
            key={i}
            style={{
              fontFamily: MONO_FONT,
              fontSize: 11,
              color: line.color,
              opacity: lineOpacity,
              whiteSpace: 'nowrap',
              lineHeight: 1.5,
            }}
          >
            {line.text}
          </div>
        );
      })}

      {/* Blinking cursor */}
      <div
        style={{
          fontFamily: MONO_FONT,
          fontSize: 11,
          color: TERMINAL_TEXT,
          opacity: Math.sin(frame * 0.2) > 0 ? 0.7 : 0,
          marginTop: 2,
        }}
      >
        ▌
      </div>
    </div>
  );
};

export default TerminalOverlay;
