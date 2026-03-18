import React from 'react';
import {interpolate, useCurrentFrame, Easing} from 'remotion';
import {
  CHART_LEFT, CHART_RIGHT, CHART_TOP, CHART_BOTTOM,
  CHART_WIDTH, CHART_HEIGHT,
  GRID_COLOR, GRID_OPACITY,
  AXIS_LABEL_COLOR,
  Y_MAX, Y_STEP,
  INITIAL_X_LABELS, FINAL_X_LABELS,
  MORPH_START, MORPH_DURATION,
} from './constants';

/**
 * Chart axes, grid lines, and x-axis labels with morph support.
 */
export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  const morphProgress = interpolate(
    frame,
    [MORPH_START, MORPH_START + MORPH_DURATION],
    [0, 1],
    {extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.bezier(0.4, 0, 0.2, 1)},
  );

  // Horizontal grid lines at $10 intervals
  const hLines: number[] = [];
  for (let v = Y_STEP; v <= Y_MAX; v += Y_STEP) {
    const y = CHART_BOTTOM - (v / Y_MAX) * CHART_HEIGHT;
    hLines.push(y);
  }

  // Vertical grid at label positions (8 positions)
  const vLineCount = 8;
  const vLines: number[] = [];
  for (let i = 0; i < vLineCount; i++) {
    vLines.push(CHART_LEFT + (i / (vLineCount - 1)) * CHART_WIDTH);
  }

  // Interpolated X labels
  const xLabels = INITIAL_X_LABELS.map((initLabel, i) => {
    const finalLabel = FINAL_X_LABELS[i] || '';
    if (morphProgress <= 0) return initLabel;
    if (morphProgress >= 1) return finalLabel;
    // During morph, fade out initial, fade in final
    return morphProgress < 0.5 ? initLabel : finalLabel;
  });

  const xLabelOpacity = (i: number) => {
    if (morphProgress <= 0 || morphProgress >= 1) return 0.5;
    // Fade through transition
    const dist = Math.abs(morphProgress - 0.5);
    return 0.5 * (dist / 0.5); // fades to 0 at midpoint, back to 0.5
  };

  // Y-axis labels
  const yLabels = [];
  for (let v = 0; v <= Y_MAX; v += Y_STEP) {
    yLabels.push({value: v, y: CHART_BOTTOM - (v / Y_MAX) * CHART_HEIGHT});
  }

  return (
    <svg
      width={1920}
      height={1080}
      style={{position: 'absolute', top: 0, left: 0}}
    >
      {/* Horizontal grid lines */}
      {hLines.map((y, i) => (
        <line
          key={`h-${i}`}
          x1={CHART_LEFT} y1={y}
          x2={CHART_RIGHT} y2={y}
          stroke={GRID_COLOR}
          strokeOpacity={GRID_OPACITY}
          strokeWidth={1}
        />
      ))}

      {/* Vertical grid lines */}
      {vLines.map((x, i) => (
        <line
          key={`v-${i}`}
          x1={x} y1={CHART_TOP}
          x2={x} y2={CHART_BOTTOM}
          stroke={GRID_COLOR}
          strokeOpacity={GRID_OPACITY}
          strokeWidth={1}
        />
      ))}

      {/* X-axis line */}
      <line
        x1={CHART_LEFT} y1={CHART_BOTTOM}
        x2={CHART_RIGHT} y2={CHART_BOTTOM}
        stroke={AXIS_LABEL_COLOR}
        strokeOpacity={0.3}
        strokeWidth={1}
      />

      {/* Y-axis line */}
      <line
        x1={CHART_LEFT} y1={CHART_TOP}
        x2={CHART_LEFT} y2={CHART_BOTTOM}
        stroke={AXIS_LABEL_COLOR}
        strokeOpacity={0.3}
        strokeWidth={1}
      />

      {/* X-axis labels */}
      {xLabels.map((label, i) => {
        if (!label) return null;
        const x = CHART_LEFT + (i / (vLineCount - 1)) * CHART_WIDTH;
        return (
          <text
            key={`xl-${i}`}
            x={x}
            y={CHART_BOTTOM + 30}
            textAnchor="middle"
            fill={AXIS_LABEL_COLOR}
            fillOpacity={xLabelOpacity(i)}
            fontSize={12}
            fontFamily="Inter, sans-serif"
          >
            {label}
          </text>
        );
      })}

      {/* Y-axis labels */}
      {yLabels.map(({value, y}) => (
        <text
          key={`yl-${value}`}
          x={CHART_LEFT - 15}
          y={y + 4}
          textAnchor="end"
          fill={AXIS_LABEL_COLOR}
          fillOpacity={0.5}
          fontSize={12}
          fontFamily="Inter, sans-serif"
        >
          ${value}
        </text>
      ))}
    </svg>
  );
};

export default ChartAxes;
