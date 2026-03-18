import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  DEBT_CURVE_COLOR,
  REGEN_COLOR,
  SAWTOOTH_BASELINE_Y,
  GAP_FILL_DURATION,
} from './constants';

export const GapGradient: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, GAP_FILL_DURATION], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <linearGradient id="gapGrad" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stopColor={DEBT_CURVE_COLOR} stopOpacity={0.04} />
          <stop offset="100%" stopColor={REGEN_COLOR} stopOpacity={0.04} />
        </linearGradient>
      </defs>
      <rect
        x={CHART_LEFT + 200}
        y={CHART_TOP + 50}
        width={CHART_RIGHT - CHART_LEFT - 200}
        height={SAWTOOTH_BASELINE_Y - CHART_TOP - 50}
        fill="url(#gapGrad)"
        opacity={opacity}
        rx={8}
      />
    </svg>
  );
};
