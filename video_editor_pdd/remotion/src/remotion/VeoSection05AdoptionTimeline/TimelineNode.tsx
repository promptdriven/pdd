import React from 'react';
import { spring, useCurrentFrame, useVideoConfig } from 'remotion';
import { COLORS, DIMENSIONS, TYPOGRAPHY } from './constants';

interface TimelineNodeProps {
  year: number;
  x: number;
  y: number;
}

export const TimelineNode: React.FC<TimelineNodeProps> = ({ year, x, y }) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Spring animation for node appearance
  const scale = spring({
    frame,
    fps,
    config: {
      damping: 15,
      stiffness: 200,
    },
  });

  // Pulse animation
  const pulseScale = 1 + Math.sin(frame / 10) * 0.05;

  return (
    <>
      {/* Node circle */}
      <svg
        width={DIMENSIONS.width}
        height={DIMENSIONS.height}
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
        }}
      >
        <defs>
          <filter id={`nodePulse-${year}`} x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation={10} result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Outer glow */}
        <circle
          cx={x}
          cy={y}
          r={DIMENSIONS.node.radius * scale * pulseScale}
          fill={COLORS.nodeFill}
          opacity={0.3}
          filter={`url(#nodePulse-${year})`}
        />

        {/* Main circle */}
        <circle
          cx={x}
          cy={y}
          r={DIMENSIONS.node.radius * scale}
          fill={COLORS.nodeFill}
          stroke={COLORS.nodeBorder}
          strokeWidth={DIMENSIONS.node.borderWidth}
        />
      </svg>

      {/* Year label */}
      <div
        style={{
          position: 'absolute',
          left: x,
          top: y + 40,
          transform: `translateX(-50%) scale(${scale})`,
          fontFamily: TYPOGRAPHY.year.fontFamily,
          fontWeight: TYPOGRAPHY.year.fontWeight,
          fontSize: TYPOGRAPHY.year.fontSize,
          color: TYPOGRAPHY.year.color,
          textAlign: 'center',
          whiteSpace: 'nowrap',
        }}
      >
        {year}
      </div>
    </>
  );
};
