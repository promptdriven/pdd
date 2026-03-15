import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, CHECKMARK, CHECKMARK_PATH, TIMING } from './constants';

export const DrawCheckmark: React.FC = () => {
  const frame = useCurrentFrame();

  // Stroke draws via dashoffset over frames 0-18 with easeInOutCubic.
  // Short leg: frames 0-7, long leg: frames 7-18.
  // We animate the full path as one continuous stroke draw.
  const drawProgress = interpolate(
    frame,
    [TIMING.checkmarkStart, TIMING.checkmarkEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const dashOffset = CHECKMARK.totalPathLength * (1 - drawProgress);

  // Glow fades in as checkmark draws (tracks draw progress)
  const glowOpacity = interpolate(
    drawProgress,
    [0, 0.5, 1],
    [0, CHECKMARK.glowOpacity, CHECKMARK.glowOpacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  const svgSize = CHECKMARK.viewBoxSize;
  // Position the SVG so its center aligns with (cx, cy) on the canvas
  const left = CHECKMARK.cx - svgSize / 2;
  const top = CHECKMARK.cy - svgSize / 2;

  return (
    <>
      {/* Glow layer behind the checkmark */}
      <div
        style={{
          position: 'absolute',
          left: CHECKMARK.cx - svgSize,
          top: CHECKMARK.cy - svgSize,
          width: svgSize * 2,
          height: svgSize * 2,
          borderRadius: '50%',
          background: `radial-gradient(circle, ${COLORS.glow} 0%, transparent 70%)`,
          opacity: glowOpacity,
          filter: `blur(${CHECKMARK.glowBlur}px)`,
          pointerEvents: 'none',
        }}
      />
      {/* Checkmark SVG */}
      <div
        style={{
          position: 'absolute',
          left,
          top,
          width: svgSize,
          height: svgSize,
        }}
      >
        <svg
          width={svgSize}
          height={svgSize}
          viewBox={`0 0 ${svgSize} ${svgSize}`}
          fill="none"
        >
          <path
            d={CHECKMARK_PATH}
            stroke={COLORS.checkmark}
            strokeWidth={CHECKMARK.strokeWidth}
            strokeLinecap="round"
            strokeLinejoin="round"
            pathLength={CHECKMARK.totalPathLength}
            strokeDasharray={CHECKMARK.totalPathLength}
            strokeDashoffset={dashOffset}
          />
        </svg>
      </div>
    </>
  );
};
