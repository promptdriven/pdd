import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  CHART_LEFT,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  GREEN_LINE_COLOR,
  REGENERATION_Y,
  GREEN_LINE_START,
  GREEN_LINE_DURATION,
} from './constants';

export const GreenLine: React.FC = () => {
  const frame = useCurrentFrame();

  const lineY = CHART_BOTTOM - REGENERATION_Y * CHART_HEIGHT;

  const drawProgress = interpolate(
    frame,
    [GREEN_LINE_START, GREEN_LINE_START + GREEN_LINE_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  const lineEndX = CHART_LEFT + CHART_WIDTH * drawProgress;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <line
        x1={CHART_LEFT}
        y1={lineY}
        x2={lineEndX}
        y2={lineY}
        stroke={GREEN_LINE_COLOR}
        strokeWidth={3}
        strokeLinecap="round"
      />
    </svg>
  );
};
