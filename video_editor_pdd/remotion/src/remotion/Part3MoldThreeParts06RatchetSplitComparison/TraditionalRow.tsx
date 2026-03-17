import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { FONT_MONO, RED, AMBER, TEXT_PRIMARY, TEXT_SECONDARY, ROW_HEIGHT } from './constants';

interface TraditionalRowProps {
  bug: string;
  fix: string;
  icon: 'x' | 'warn';
  appearFrame: number;
  y: number;
}

export const TraditionalRow: React.FC<TraditionalRowProps> = ({
  bug,
  fix,
  icon,
  appearFrame,
  y,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(frame, [appearFrame, appearFrame + 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  if (progress <= 0) return null;

  const translateX = interpolate(progress, [0, 1], [-20, 0]);
  const opacity = progress;

  const iconColor = icon === 'x' ? RED : AMBER;
  const iconChar = icon === 'x' ? '✗' : '⚠';

  return (
    <div
      style={{
        position: 'absolute',
        top: y,
        left: 20,
        right: 20,
        height: ROW_HEIGHT,
        display: 'flex',
        alignItems: 'center',
        gap: 12,
        opacity,
        transform: `translateX(${translateX}px)`,
      }}
    >
      {/* Status icon */}
      <div
        style={{
          width: 24,
          height: 24,
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
          fontSize: 16,
          color: iconColor,
          flexShrink: 0,
        }}
      >
        {iconChar}
      </div>

      {/* Text content */}
      <div style={{ display: 'flex', flexDirection: 'column', gap: 2, minWidth: 0 }}>
        <div
          style={{
            fontFamily: FONT_MONO,
            fontSize: 12,
            color: TEXT_PRIMARY,
            whiteSpace: 'nowrap',
            overflow: 'hidden',
            textOverflow: 'ellipsis',
          }}
        >
          {bug}
        </div>
        <div
          style={{
            fontFamily: FONT_MONO,
            fontSize: 10,
            color: TEXT_SECONDARY,
            opacity: 0.5,
            whiteSpace: 'nowrap',
            overflow: 'hidden',
            textOverflow: 'ellipsis',
          }}
        >
          → {fix}
        </div>
      </div>
    </div>
  );
};
