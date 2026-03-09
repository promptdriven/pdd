import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { CANVAS, COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const BorderTrace: React.FC = () => {
  const frame = useCurrentFrame();

  const { borderLeft, borderTop, borderRight, borderBottom, borderStroke } = DIMENSIONS;
  const {
    borderStart,
    borderTopEnd,
    borderRightEnd,
    borderBottomEnd,
    borderLeftEnd,
  } = ANIMATION_TIMING;

  const topWidth = borderRight - borderLeft;
  const sideHeight = borderBottom - borderTop;

  // Each segment draws linearly over its time range
  const topProgress = interpolate(frame, [borderStart, borderTopEnd], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const rightProgress = interpolate(frame, [borderTopEnd, borderRightEnd], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const bottomProgress = interpolate(frame, [borderRightEnd, borderBottomEnd], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const leftProgress = interpolate(frame, [borderBottomEnd, borderLeftEnd], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Glow filter for leading edge
  const glowFilterId = 'borderGlow';

  return (
    <svg
      width={CANVAS.width}
      height={CANVAS.height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <filter id={glowFilterId} x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="4" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Top edge: left to right */}
      {topProgress > 0 && (
        <line
          x1={borderLeft}
          y1={borderTop}
          x2={borderLeft + topWidth * topProgress}
          y2={borderTop}
          stroke={COLORS.borderFrame}
          strokeWidth={borderStroke}
          filter={topProgress < 1 ? `url(#${glowFilterId})` : undefined}
        />
      )}

      {/* Right edge: top to bottom */}
      {rightProgress > 0 && (
        <line
          x1={borderRight}
          y1={borderTop}
          x2={borderRight}
          y2={borderTop + sideHeight * rightProgress}
          stroke={COLORS.borderFrame}
          strokeWidth={borderStroke}
          filter={rightProgress < 1 ? `url(#${glowFilterId})` : undefined}
        />
      )}

      {/* Bottom edge: right to left */}
      {bottomProgress > 0 && (
        <line
          x1={borderRight}
          y1={borderBottom}
          x2={borderRight - topWidth * bottomProgress}
          y2={borderBottom}
          stroke={COLORS.borderFrame}
          strokeWidth={borderStroke}
          filter={bottomProgress < 1 ? `url(#${glowFilterId})` : undefined}
        />
      )}

      {/* Left edge: bottom to top */}
      {leftProgress > 0 && (
        <line
          x1={borderLeft}
          y1={borderBottom}
          x2={borderLeft}
          y2={borderBottom - sideHeight * leftProgress}
          stroke={COLORS.borderFrame}
          strokeWidth={borderStroke}
          filter={leftProgress < 1 ? `url(#${glowFilterId})` : undefined}
        />
      )}
    </svg>
  );
};
