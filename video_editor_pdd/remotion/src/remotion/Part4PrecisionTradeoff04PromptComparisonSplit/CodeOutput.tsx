import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, CANVAS_WIDTH, GENERATED_CODE_LINES } from './constants';

interface CodeOutputProps {
  startFrame: number;
}

export const CodeOutput: React.FC<CodeOutputProps> = ({ startFrame }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [startFrame, startFrame + 20],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  if (frame < startFrame) return null;

  const codeLineHeight = 16;
  const panelWidth = 440;
  const codeY = 870;

  return (
    <div style={{ opacity }}>
      {/* Left code block */}
      <div
        style={{
          position: 'absolute',
          left: 40,
          top: codeY,
          width: panelWidth,
          backgroundColor: 'rgba(15, 23, 42, 0.6)',
          borderRadius: 4,
          padding: '8px 12px',
          border: '1px solid rgba(51, 65, 85, 0.2)',
        }}
      >
        {GENERATED_CODE_LINES.map((line, i) => (
          <div
            key={i}
            style={{
              fontFamily: '"JetBrains Mono", monospace',
              fontSize: 9,
              color: COLORS.codeOutputColor,
              opacity: 0.3,
              height: codeLineHeight,
              whiteSpace: 'pre',
            }}
          >
            {line}
          </div>
        ))}
      </div>

      {/* Right code block */}
      <div
        style={{
          position: 'absolute',
          left: CANVAS_WIDTH / 2 + 40,
          top: codeY,
          width: panelWidth,
          backgroundColor: 'rgba(15, 23, 42, 0.6)',
          borderRadius: 4,
          padding: '8px 12px',
          border: '1px solid rgba(51, 65, 85, 0.2)',
        }}
      >
        {GENERATED_CODE_LINES.map((line, i) => (
          <div
            key={i}
            style={{
              fontFamily: '"JetBrains Mono", monospace',
              fontSize: 9,
              color: COLORS.codeOutputColor,
              opacity: 0.3,
              height: codeLineHeight,
              whiteSpace: 'pre',
            }}
          >
            {line}
          </div>
        ))}
      </div>

      {/* Center label */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: codeY + GENERATED_CODE_LINES.length * codeLineHeight + 30,
          width: CANVAS_WIDTH,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 13,
          color: COLORS.bottomLabelColor,
          opacity: 0.5,
        }}
      >
        Same output. Different specification strategy.
      </div>
    </div>
  );
};
