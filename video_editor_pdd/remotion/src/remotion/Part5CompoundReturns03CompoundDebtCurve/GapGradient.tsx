import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  WIDTH,
  HEIGHT,
  DEBT_CURVE_COLOR,
  REGEN_COLOR,
  GAP_FILL_START,
  GAP_FILL_DURATION,
  CHART_RIGHT,
  SAWTOOTH_BASELINE_Y,
  buildExponentialCurvePixels,
} from './constants';

export const GapGradient: React.FC = () => {
  const frame = useCurrentFrame();
  const curvePoints = useMemo(() => buildExponentialCurvePixels(100), []);

  const fillOpacity = interpolate(
    frame,
    [GAP_FILL_START, GAP_FILL_START + GAP_FILL_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  if (fillOpacity <= 0) return null;

  // Build the area between the exponential curve (top) and the sawtooth baseline (bottom)
  // Use the right portion of the chart where the gap is most visible
  const startIdx = Math.floor(curvePoints.length * 0.3);
  const areaPoints = curvePoints.slice(startIdx);

  // Build SVG path: along the curve top, then along the baseline bottom (reversed)
  let pathD = `M ${areaPoints[0].x} ${areaPoints[0].y}`;
  for (let i = 1; i < areaPoints.length; i++) {
    pathD += ` L ${areaPoints[i].x} ${areaPoints[i].y}`;
  }
  // Close along the bottom baseline
  pathD += ` L ${CHART_RIGHT} ${SAWTOOTH_BASELINE_Y}`;
  pathD += ` L ${areaPoints[0].x} ${SAWTOOTH_BASELINE_Y}`;
  pathD += ' Z';

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <linearGradient id="gapGradient" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stopColor={DEBT_CURVE_COLOR} stopOpacity={0.04} />
          <stop offset="100%" stopColor={REGEN_COLOR} stopOpacity={0.04} />
        </linearGradient>
      </defs>
      <path
        d={pathD}
        fill="url(#gapGradient)"
        opacity={fillOpacity}
      />
    </svg>
  );
};
