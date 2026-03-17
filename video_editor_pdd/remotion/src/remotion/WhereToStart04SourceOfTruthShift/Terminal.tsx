import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, TIMING, LAYOUT } from './constants';

/**
 * Terminal widget in the bottom-right corner showing test results.
 * Fades in at the terminal start frame.
 */
export const Terminal: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [TIMING.terminalStart, TIMING.terminalStart + TIMING.terminalFadeDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const { terminal } = LAYOUT;

  return (
    <div
      style={{
        position: 'absolute',
        left: terminal.x,
        top: terminal.y,
        width: terminal.width,
        height: terminal.height,
        opacity,
        borderRadius: 6,
        overflow: 'hidden',
        border: '1px solid rgba(51, 65, 85, 0.3)',
      }}
    >
      {/* Terminal title bar */}
      <div
        style={{
          height: 20,
          backgroundColor: COLORS.titleBar,
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 8,
          gap: 4,
        }}
      >
        {COLORS.titleBarDots.map((color, i) => (
          <div
            key={i}
            style={{
              width: 6,
              height: 6,
              borderRadius: '50%',
              backgroundColor: color,
              opacity: 0.5,
            }}
          />
        ))}
        <span
          style={{
            flex: 1,
            textAlign: 'center',
            fontFamily: '"JetBrains Mono", monospace',
            fontSize: 8,
            color: COLORS.terminalText,
            opacity: 0.4,
          }}
        >
          terminal
        </span>
      </div>

      {/* Terminal body */}
      <div
        style={{
          backgroundColor: '#0B1120',
          padding: '8px 12px',
          height: terminal.height - 20,
          display: 'flex',
          flexDirection: 'column',
          justifyContent: 'center',
        }}
      >
        <div
          style={{
            fontFamily: '"JetBrains Mono", monospace',
            fontSize: 10,
            color: COLORS.terminalText,
            opacity: 0.5,
            marginBottom: 4,
          }}
        >
          $ pdd test auth_handler
        </div>
        <div
          style={{
            fontFamily: '"JetBrains Mono", monospace',
            fontSize: 10,
            color: COLORS.terminalSuccess,
            opacity: 0.5,
          }}
        >
          ✓ 3/3 passing
        </div>
      </div>
    </div>
  );
};

export default Terminal;
