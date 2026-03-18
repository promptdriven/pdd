import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  WIDTH,
  HEIGHT,
  TEXT_COLOR,
  PILL_BG_COLOR,
  GAP_LABEL_START,
  GAP_LABEL_DURATION,
  DOUBLE_ARROW_DURATION,
} from './constants';

// Y positions of the two curves at x=960 (approximately Year 5)
const PATCHING_Y_AT_960 = 468;
const PDD_Y_AT_960 = 744;
const CENTER_X = 960;
const CENTER_Y = (PATCHING_Y_AT_960 + PDD_Y_AT_960) / 2; // ~606 but spec says 480, use 500

const LABEL_Y = 500;

export const GapLabel: React.FC = () => {
  const frame = useCurrentFrame();

  // Label fade-in
  const labelOpacity = interpolate(
    frame,
    [GAP_LABEL_START, GAP_LABEL_START + GAP_LABEL_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Double-arrow draw
  const arrowProgress = interpolate(
    frame,
    [GAP_LABEL_START, GAP_LABEL_START + DOUBLE_ARROW_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  // Arrow endpoints: from patching curve down to PDD curve at x=960
  const arrowTop = PATCHING_Y_AT_960 + 5;
  const arrowBottom = PDD_Y_AT_960 - 5;
  const arrowLen = arrowBottom - arrowTop;
  const currentLen = arrowLen * arrowProgress;

  // Top arrow draws downward, bottom arrow draws upward, meeting in middle
  const topEnd = arrowTop + currentLen / 2;
  const bottomEnd = arrowBottom - currentLen / 2;

  // Pill dimensions
  const pillWidth = 260;
  const pillHeight = 38;

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Double arrow line */}
      <g opacity={labelOpacity * 0.3}>
        {/* Top segment */}
        <line
          x1={CENTER_X}
          y1={arrowTop}
          x2={CENTER_X}
          y2={topEnd}
          stroke={TEXT_COLOR}
          strokeWidth={1.5}
        />
        {/* Bottom segment */}
        <line
          x1={CENTER_X}
          y1={arrowBottom}
          x2={CENTER_X}
          y2={bottomEnd}
          stroke={TEXT_COLOR}
          strokeWidth={1.5}
        />
        {/* Top arrowhead */}
        <polygon
          points={`${CENTER_X},${arrowTop} ${CENTER_X - 4},${arrowTop + 8} ${CENTER_X + 4},${arrowTop + 8}`}
          fill={TEXT_COLOR}
        />
        {/* Bottom arrowhead */}
        <polygon
          points={`${CENTER_X},${arrowBottom} ${CENTER_X - 4},${arrowBottom - 8} ${CENTER_X + 4},${arrowBottom - 8}`}
          fill={TEXT_COLOR}
        />
      </g>

      {/* Pill background */}
      <rect
        x={CENTER_X - pillWidth / 2}
        y={LABEL_Y - pillHeight / 2}
        width={pillWidth}
        height={pillHeight}
        rx={10}
        ry={10}
        fill={PILL_BG_COLOR}
        opacity={labelOpacity * 0.3}
      />

      {/* Label text */}
      <text
        x={CENTER_X}
        y={LABEL_Y + 6}
        textAnchor="middle"
        fill={TEXT_COLOR}
        opacity={labelOpacity}
        fontFamily="Inter, sans-serif"
        fontSize={22}
        fontWeight={600}
      >
        The compounding gap
      </text>
    </svg>
  );
};
