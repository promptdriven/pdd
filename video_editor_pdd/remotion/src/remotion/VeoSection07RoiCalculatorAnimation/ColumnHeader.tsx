import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { LAYOUT, COLORS, TYPOGRAPHY } from './constants';

interface ColumnHeaderProps {
  x: number;
  text: string;
  delay: number;
}

export const ColumnHeader: React.FC<ColumnHeaderProps> = ({ x, text, delay }) => {
  const frame = useCurrentFrame();

  // Slide in from top with easeOutBack
  const offsetY = interpolate(
    frame,
    [delay, delay + 20],
    [-150, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.7)),
    }
  );

  const opacity = interpolate(
    frame,
    [delay, delay + 10],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: LAYOUT.columnHeader.y + offsetY,
        width: LAYOUT.columnHeader.width,
        height: LAYOUT.columnHeader.height,
        backgroundColor: COLORS.columnHeader.background,
        border: `${LAYOUT.columnHeader.borderWidth}px solid ${COLORS.columnHeader.border}`,
        borderRadius: LAYOUT.columnHeader.borderRadius,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        opacity,
      }}
    >
      <span
        style={{
          fontFamily: TYPOGRAPHY.columnHeader.family,
          fontWeight: TYPOGRAPHY.columnHeader.weight,
          fontSize: TYPOGRAPHY.columnHeader.size,
          color: COLORS.columnHeader.text,
        }}
      >
        {text}
      </span>
    </div>
  );
};
