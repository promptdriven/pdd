import React from 'react';
import {interpolate, useCurrentFrame, Easing} from 'remotion';
import {
  CHART_LEFT, CHART_BOTTOM,
  CHART_WIDTH, CHART_HEIGHT,
  Y_MAX,
  CROSSING_COLOR, CROSSING_GLOW_OPACITY,
  CROSSING_RADIUS, CROSSING_GLOW_RADIUS,
  PULSE_CYCLE, PULSE_SCALE_MIN, PULSE_SCALE_MAX,
  PULSE_START,
  MORPH_START, MORPH_DURATION,
  RELABEL_START, RELABEL_END,
  INITIAL_CROSSING_X_NORM, INITIAL_CROSSING_Y_NORM,
  FINAL_CROSSING_X_NORM, FINAL_CROSSING_Y_NORM,
  INITIAL_CROSSING_LABEL, FINAL_CROSSING_LABEL,
  INITIAL_POST_LABEL, FINAL_POST_LABEL,
} from './constants';

/**
 * The crossing point with pulsing glow, label morph,
 * and post-crossing zone label.
 */
export const CrossingPoint: React.FC = () => {
  const frame = useCurrentFrame();

  const morphProgress = interpolate(
    frame,
    [MORPH_START, MORPH_START + MORPH_DURATION],
    [0, 1],
    {extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.bezier(0.4, 0, 0.2, 1)},
  );

  // Crossing position interpolation
  const crossingXNorm =
    INITIAL_CROSSING_X_NORM +
    (FINAL_CROSSING_X_NORM - INITIAL_CROSSING_X_NORM) * morphProgress;
  const crossingYNorm =
    INITIAL_CROSSING_Y_NORM +
    (FINAL_CROSSING_Y_NORM - INITIAL_CROSSING_Y_NORM) * morphProgress;

  const cx = CHART_LEFT + crossingXNorm * CHART_WIDTH;
  const cy = CHART_BOTTOM - crossingYNorm * CHART_HEIGHT;

  // Pulse animation (starts at PULSE_START, repeats every PULSE_CYCLE)
  const pulseFrame = Math.max(0, frame - PULSE_START);
  const cyclePos = (pulseFrame % PULSE_CYCLE) / PULSE_CYCLE;
  const pulseScale = interpolate(
    cyclePos,
    [0, 0.5, 1],
    [PULSE_SCALE_MIN, PULSE_SCALE_MAX, PULSE_SCALE_MIN],
    {extrapolateLeft: 'clamp', extrapolateRight: 'clamp'},
  );
  const showPulse = frame >= PULSE_START;

  // Crossing label morph
  const labelMorphProgress = interpolate(
    frame,
    [MORPH_START + 30, MORPH_START + 90],
    [0, 1],
    {extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.bezier(0.4, 0, 0.2, 1)},
  );

  const crossingLabel = labelMorphProgress < 0.5
    ? INITIAL_CROSSING_LABEL
    : FINAL_CROSSING_LABEL;

  const labelOpacity = labelMorphProgress < 0.4
    ? 1
    : labelMorphProgress < 0.6
      ? 1 - (labelMorphProgress - 0.4) / 0.2
      : interpolate(labelMorphProgress, [0.6, 0.8], [0, 1], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        });

  // Post-crossing label
  const postLabelProgress = interpolate(
    frame,
    [RELABEL_START, RELABEL_END],
    [0, 1],
    {extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.bezier(0.4, 0, 0.2, 1)},
  );

  const postLabel = postLabelProgress < 0.5
    ? INITIAL_POST_LABEL
    : FINAL_POST_LABEL;

  const postLabelOpacity = postLabelProgress < 0.4
    ? 0.5
    : postLabelProgress < 0.6
      ? 0.5 * (1 - (postLabelProgress - 0.4) / 0.2)
      : interpolate(postLabelProgress, [0.6, 0.8], [0, 0.5], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        });

  // Post-crossing label X position: right of crossing
  const postLabelX = cx + 80;
  const postLabelY = cy + 60;

  return (
    <svg
      width={1920}
      height={1080}
      style={{position: 'absolute', top: 0, left: 0}}
    >
      <defs>
        <filter id="crossingGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation={CROSSING_GLOW_RADIUS / 2} result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {showPulse && (
        <g transform={`translate(${cx}, ${cy}) scale(${pulseScale}) translate(${-cx}, ${-cy})`}>
          {/* Glow circle */}
          <circle
            cx={cx}
            cy={cy}
            r={CROSSING_GLOW_RADIUS}
            fill={CROSSING_COLOR}
            fillOpacity={CROSSING_GLOW_OPACITY}
            filter="url(#crossingGlow)"
          />

          {/* Main crossing point circle */}
          <circle
            cx={cx}
            cy={cy}
            r={CROSSING_RADIUS}
            fill="none"
            stroke={CROSSING_COLOR}
            strokeWidth={3}
            strokeOpacity={0.9}
          />

          {/* Center dot */}
          <circle
            cx={cx}
            cy={cy}
            r={4}
            fill={CROSSING_COLOR}
            fillOpacity={0.9}
          />
        </g>
      )}

      {/* Crossing label */}
      <text
        x={cx}
        y={cy - 30}
        textAnchor="middle"
        fill={CROSSING_COLOR}
        fillOpacity={labelOpacity}
        fontSize={crossingLabel === FINAL_CROSSING_LABEL ? 18 : 14}
        fontWeight={crossingLabel === FINAL_CROSSING_LABEL ? 700 : 400}
        fontFamily="Inter, sans-serif"
      >
        {crossingLabel}
      </text>

      {/* Post-crossing zone label */}
      <text
        x={postLabelX}
        y={postLabelY}
        textAnchor="middle"
        fill="#EF4444"
        fillOpacity={postLabelOpacity}
        fontSize={13}
        fontFamily="Inter, sans-serif"
        fontStyle="italic"
      >
        {postLabel}
      </text>
    </svg>
  );
};

export default CrossingPoint;
