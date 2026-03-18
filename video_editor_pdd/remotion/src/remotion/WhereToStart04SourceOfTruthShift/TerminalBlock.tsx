import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, TERMINAL, TIMING } from './constants';

/**
 * A small terminal window showing test results.
 * Fades in at TIMING.terminalStart.
 */
const TerminalBlock: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [TIMING.terminalStart, TIMING.terminalStart + TIMING.terminalDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: TERMINAL.x,
        top: TERMINAL.y,
        width: TERMINAL.width,
        height: TERMINAL.height,
        backgroundColor: '#0F172A',
        borderRadius: 6,
        border: '1px solid rgba(51, 65, 85, 0.3)',
        opacity,
        overflow: 'hidden',
      }}
    >
      {/* Terminal title bar */}
      <div
        style={{
          height: 18,
          backgroundColor: COLORS.titleBar,
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 8,
          gap: 4,
        }}
      >
        <div style={{ width: 5, height: 5, borderRadius: '50%', backgroundColor: '#EF4444', opacity: 0.5 }} />
        <div style={{ width: 5, height: 5, borderRadius: '50%', backgroundColor: '#F59E0B', opacity: 0.5 }} />
        <div style={{ width: 5, height: 5, borderRadius: '50%', backgroundColor: '#22C55E', opacity: 0.5 }} />
        <span
          style={{
            marginLeft: 6,
            fontFamily: '"JetBrains Mono", monospace',
            fontSize: 8,
            color: COLORS.codeText,
            opacity: 0.4,
          }}
        >
          terminal
        </span>
      </div>

      {/* Terminal content */}
      <div style={{ padding: '8px 10px' }}>
        <div
          style={{
            fontFamily: '"JetBrains Mono", monospace',
            fontSize: 10,
            color: COLORS.codeText,
            opacity: 0.5,
          }}
        >
          $ pdd test auth_handler
        </div>
        <div
          style={{
            fontFamily: '"JetBrains Mono", monospace',
            fontSize: 10,
            color: COLORS.success,
            opacity: 0.5,
            marginTop: 4,
          }}
        >
          ✓ 3/3 passing
        </div>
      </div>
    </div>
  );
};

export default TerminalBlock;
