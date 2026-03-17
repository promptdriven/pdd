import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CHART,
  TIMING,
  COLORS,
  interpolateY,
  PATCHING_POINTS,
  PDD_POINTS,
} from './constants';

export const GapLabel: React.FC = () => {
  const frame = useCurrentFrame();

  const localFrame = frame - TIMING.gapLabelStart;
  if (localFrame < 0) return null;

  // Fade in
  const fadeProgress = interpolate(
    localFrame,
    [0, TIMING.gapLabelDuration],
    [0, 1],
    { extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Double-arrow draw progress
  const arrowDraw = interpolate(
    localFrame,
    [0, 20],
    [0, 1],
    { extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  const centerX = 960;
  const patchY = interpolateY(PATCHING_POINTS, centerX);
  const pddY = interpolateY(PDD_POINTS, centerX);
  const labelY = (patchY + pddY) / 2;

  // Arrow extents
  const arrowTopY = patchY + 10;
  const arrowBottomY = pddY - 10;
  const arrowCurrentTop = arrowBottomY - (arrowBottomY - arrowTopY) * arrowDraw;
  const arrowCurrentBottom = arrowTopY + (arrowBottomY - arrowTopY) * arrowDraw;

  const arrowHeadSize = 6;

  return (
    <svg
      width={CHART.width}
      height={CHART.height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <g opacity={fadeProgress}>
        {/* Vertical double-arrow line */}
        <line
          x1={centerX}
          y1={arrowCurrentTop}
          x2={centerX}
          y2={arrowCurrentBottom}
          stroke={COLORS.text}
          strokeWidth={1.5}
          opacity={0.3}
        />

        {/* Top arrowhead */}
        {arrowDraw > 0.5 && (
          <polygon
            points={`${centerX},${arrowTopY} ${centerX - arrowHeadSize},${arrowTopY + arrowHeadSize * 1.5} ${centerX + arrowHeadSize},${arrowTopY + arrowHeadSize * 1.5}`}
            fill={COLORS.text}
            opacity={0.3 * Math.min(1, (arrowDraw - 0.5) * 2)}
          />
        )}

        {/* Bottom arrowhead */}
        {arrowDraw > 0.5 && (
          <polygon
            points={`${centerX},${arrowBottomY} ${centerX - arrowHeadSize},${arrowBottomY - arrowHeadSize * 1.5} ${centerX + arrowHeadSize},${arrowBottomY - arrowHeadSize * 1.5}`}
            fill={COLORS.text}
            opacity={0.3 * Math.min(1, (arrowDraw - 0.5) * 2)}
          />
        )}

        {/* Pill background */}
        <rect
          x={centerX - 140}
          y={labelY - 18}
          width={280}
          height={36}
          rx={10}
          ry={10}
          fill={COLORS.pillBg}
          opacity={0.3}
        />

        {/* Label text */}
        <text
          x={centerX}
          y={labelY + 6}
          textAnchor="middle"
          fontFamily="Inter, sans-serif"
          fontSize={22}
          fontWeight={600}
          fill={COLORS.text}
        >
          The compounding gap
        </text>
      </g>
    </svg>
  );
};
