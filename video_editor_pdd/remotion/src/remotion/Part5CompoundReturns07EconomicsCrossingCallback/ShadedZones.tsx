import React from 'react';
import {interpolate, useCurrentFrame, Easing} from 'remotion';
import {
  CHART_LEFT, CHART_BOTTOM, CHART_TOP,
  CHART_WIDTH, CHART_HEIGHT,
  Y_MAX,
  GREEN_ZONE, RED_ZONE,
  MORPH_START, MORPH_DURATION,
  INITIAL_CROSSING_X_NORM, FINAL_CROSSING_X_NORM,
} from './constants';

/**
 * Shaded areas before/after the crossing point.
 * Green before crossing, red after crossing.
 */
export const ShadedZones: React.FC = () => {
  const frame = useCurrentFrame();

  const morphProgress = interpolate(
    frame,
    [MORPH_START, MORPH_START + MORPH_DURATION],
    [0, 1],
    {extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.bezier(0.4, 0, 0.2, 1)},
  );

  const crossingXNorm =
    INITIAL_CROSSING_X_NORM +
    (FINAL_CROSSING_X_NORM - INITIAL_CROSSING_X_NORM) * morphProgress;

  const crossingX = CHART_LEFT + crossingXNorm * CHART_WIDTH;

  return (
    <svg
      width={1920}
      height={1080}
      style={{position: 'absolute', top: 0, left: 0}}
    >
      {/* Green zone — pre-crossing */}
      <rect
        x={CHART_LEFT}
        y={CHART_TOP}
        width={Math.max(0, crossingX - CHART_LEFT)}
        height={CHART_HEIGHT}
        fill={GREEN_ZONE}
        fillOpacity={0.06}
      />

      {/* Red zone — post-crossing */}
      <rect
        x={crossingX}
        y={CHART_TOP}
        width={Math.max(0, CHART_LEFT + CHART_WIDTH - crossingX)}
        height={CHART_HEIGHT}
        fill={RED_ZONE}
        fillOpacity={0.06}
      />
    </svg>
  );
};

export default ShadedZones;
