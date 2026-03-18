import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, PROMPT_LINES } from './constants';

export const PromptDocument: React.FC<{
  fadeInStart: number;
  highlightStart: number;
}> = ({ fadeInStart, highlightStart }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [fadeInStart, fadeInStart + 20],
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
        left: 280,
        top: 155,
        width: 400,
        height: 250,
        backgroundColor: `rgba(30, 41, 59, 0.3)`,
        borderRadius: 4,
        opacity,
        overflow: 'hidden',
      }}
    >
      {/* Header */}
      <div
        style={{
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 10,
          color: COLORS.amber,
          opacity: 0.4,
          padding: '8px 12px 4px',
          borderBottom: '1px solid rgba(30, 41, 59, 0.5)',
        }}
      >
        prompt.md
      </div>

      {/* Content */}
      <div style={{ padding: '8px 12px' }}>
        {PROMPT_LINES.map((line, i) => {
          const isHighlighted = line.highlight;

          // Highlight animation for key phrases
          const highlightProgress = isHighlighted
            ? interpolate(
                frame,
                [highlightStart, highlightStart + 30],
                [0, 1],
                {
                  extrapolateLeft: 'clamp',
                  extrapolateRight: 'clamp',
                  easing: Easing.out(Easing.quad),
                }
              )
            : 0;

          const textColor = isHighlighted
            ? interpolateColor(highlightProgress, COLORS.textLight, COLORS.amber)
            : COLORS.textLight;

          const textOpacity = isHighlighted
            ? 0.6 + highlightProgress * 0.15
            : 0.6;

          if (line.text === '') {
            return <div key={i} style={{ height: 6 }} />;
          }

          return (
            <div
              key={i}
              style={{
                fontFamily: 'Inter, sans-serif',
                fontSize: 12,
                lineHeight: '16px',
                color: textColor,
                opacity: textOpacity,
              }}
            >
              {line.text}
            </div>
          );
        })}
      </div>
    </div>
  );
};

/** Simple hex color interpolation */
function interpolateColor(t: number, from: string, to: string): string {
  const f = hexToRgb(from);
  const tt = hexToRgb(to);
  const r = Math.round(f.r + (tt.r - f.r) * t);
  const g = Math.round(f.g + (tt.g - f.g) * t);
  const b = Math.round(f.b + (tt.b - f.b) * t);
  return `rgb(${r}, ${g}, ${b})`;
}

function hexToRgb(hex: string) {
  const h = hex.replace('#', '');
  return {
    r: parseInt(h.substring(0, 2), 16),
    g: parseInt(h.substring(2, 4), 16),
    b: parseInt(h.substring(4, 6), 16),
  };
}
