import React from 'react';
import {interpolate, useCurrentFrame, Easing} from 'remotion';
import {
  NEEDLE_START, NEEDLE_SCALE_DURATION,
  STRIKETHROUGH_START, STRIKETHROUGH_DURATION,
  NEEDLE_X, NEEDLE_Y,
  NEEDLE_COLOR, STRIKETHROUGH_COLOR,
} from './constants';

/**
 * Darning needle icon with a red strikethrough.
 * Appears at NEEDLE_START with a back-easing scale-in,
 * then the strikethrough draws across at STRIKETHROUGH_START.
 */
export const DarningNeedle: React.FC = () => {
  const frame = useCurrentFrame();

  // Needle scale-in with back easing
  const needleRawProgress = interpolate(
    frame,
    [NEEDLE_START, NEEDLE_START + NEEDLE_SCALE_DURATION],
    [0, 1],
    {extrapolateLeft: 'clamp', extrapolateRight: 'clamp'},
  );

  // Manual back easing: overshoot by 1.3
  const s = 1.3;
  const needleScale = needleRawProgress === 0
    ? 0
    : needleRawProgress >= 1
      ? 1
      : (() => {
          const t = needleRawProgress;
          // easeOut back: 1 - (1-t)^2 * ((s+1)*(1-t) - s)
          const inv = 1 - t;
          return 1 - inv * inv * ((s + 1) * inv - s);
        })();

  // Strikethrough draw progress
  const strikeProgress = interpolate(
    frame,
    [STRIKETHROUGH_START, STRIKETHROUGH_START + STRIKETHROUGH_DURATION],
    [0, 1],
    {extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad)},
  );

  const visible = frame >= NEEDLE_START;
  if (!visible) return null;

  // Needle dimensions
  const needleLength = 60;
  const eyeRadius = 6;

  // Needle is drawn as a diagonal line pointing upper-left to lower-right
  // with an eye loop at the top
  const nx = NEEDLE_X;
  const ny = NEEDLE_Y;

  // Strikethrough line endpoints (diagonal across needle)
  const strikeX1 = nx - 25;
  const strikeY1 = ny + 20;
  const strikeX2 = nx + 25;
  const strikeY2 = ny - 20;

  // Interpolated strike endpoint
  const currentStrikeX2 = strikeX1 + (strikeX2 - strikeX1) * strikeProgress;
  const currentStrikeY2 = strikeY1 + (strikeY2 - strikeY1) * strikeProgress;

  return (
    <svg
      width={1920}
      height={1080}
      style={{position: 'absolute', top: 0, left: 0}}
    >
      <g
        transform={`translate(${nx}, ${ny}) scale(${needleScale}) translate(${-nx}, ${-ny})`}
        opacity={0.4}
      >
        {/* Needle shaft — diagonal line */}
        <line
          x1={nx - needleLength / 2 * 0.7}
          y1={ny + needleLength / 2 * 0.7}
          x2={nx + needleLength / 2 * 0.7}
          y2={ny - needleLength / 2 * 0.7}
          stroke={NEEDLE_COLOR}
          strokeWidth={2.5}
          strokeLinecap="round"
        />

        {/* Needle eye — small oval at top */}
        <ellipse
          cx={nx + needleLength / 2 * 0.7 - 2}
          cy={ny - needleLength / 2 * 0.7 + 2}
          rx={eyeRadius * 0.6}
          ry={eyeRadius}
          fill="none"
          stroke={NEEDLE_COLOR}
          strokeWidth={1.5}
          transform={`rotate(-45, ${nx + needleLength / 2 * 0.7 - 2}, ${ny - needleLength / 2 * 0.7 + 2})`}
        />

        {/* Needle point — small triangle at bottom */}
        <line
          x1={nx - needleLength / 2 * 0.7}
          y1={ny + needleLength / 2 * 0.7}
          x2={nx - needleLength / 2 * 0.7 - 3}
          y2={ny + needleLength / 2 * 0.7 + 5}
          stroke={NEEDLE_COLOR}
          strokeWidth={2}
          strokeLinecap="round"
        />
      </g>

      {/* Strikethrough line */}
      {strikeProgress > 0 && (
        <line
          x1={strikeX1}
          y1={strikeY1}
          x2={currentStrikeX2}
          y2={currentStrikeY2}
          stroke={STRIKETHROUGH_COLOR}
          strokeWidth={2.5}
          strokeOpacity={0.5}
          strokeLinecap="round"
        />
      )}
    </svg>
  );
};

export default DarningNeedle;
