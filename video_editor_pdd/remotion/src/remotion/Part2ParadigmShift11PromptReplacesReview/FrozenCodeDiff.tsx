import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIFF_LINES } from './constants';

export const FrozenCodeDiff: React.FC<{
  fadeInStart: number;
}> = ({ fadeInStart }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [fadeInStart, fadeInStart + 20],
    [0, 0.15],
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
        left: 40,
        top: 80,
        width: 880,
        height: 770,
        opacity,
        overflow: 'hidden',
      }}
    >
      {DIFF_LINES.map((line, i) => {
        const color =
          line.type === 'add'
            ? '#4ADE80'
            : line.type === 'remove'
            ? '#F87171'
            : COLORS.codeMuted;

        const bgColor =
          line.type === 'add'
            ? 'rgba(34, 197, 94, 0.06)'
            : line.type === 'remove'
            ? 'rgba(239, 68, 68, 0.06)'
            : 'transparent';

        const prefix =
          line.type === 'add' ? '+ ' : line.type === 'remove' ? '- ' : '  ';

        return (
          <div
            key={i}
            style={{
              fontFamily: 'JetBrains Mono, monospace',
              fontSize: 10,
              lineHeight: '14px',
              color,
              backgroundColor: bgColor,
              whiteSpace: 'pre',
              paddingLeft: 8,
            }}
          >
            {prefix}
            {line.text}
          </div>
        );
      })}
    </div>
  );
};
