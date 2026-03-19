import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  MARGIN_LEFT,
  MARGIN_TOP,
  CHART_WIDTH,
  CHART_HEIGHT,
  AXIS_COLOR,
  AXIS_OPACITY,
  GRID_COLOR,
  GRID_OPACITY,
  LABEL_COLOR,
  LABEL_OPACITY,
  TICK_LABEL_OPACITY,
  FONT_FAMILY,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
  AXES_START,
  AXES_DURATION,
} from './constants';

/** Map data‑space X → pixel X inside the chart area */
export const xToPixel = (x: number): number =>
  MARGIN_LEFT + ((x - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;

/** Map data‑space Y → pixel Y inside the chart area */
export const yToPixel = (y: number): number =>
  MARGIN_TOP + ((Y_MAX - y) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  // Progress 0→1 for axis draw animation (easeOut cubic)
  const progress = interpolate(
    frame,
    [AXES_START, AXES_START + AXES_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) },
  );

  const gridFade = interpolate(
    frame,
    [AXES_START + 10, AXES_START + AXES_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) },
  );

  // ── Derived positions ──────────────────────────────────────────────────
  const originX = MARGIN_LEFT;
  const originY = MARGIN_TOP + CHART_HEIGHT;
  const xEnd = MARGIN_LEFT + CHART_WIDTH;
  const yEnd = MARGIN_TOP;

  // X-axis draws left → right
  const xAxisRight = originX + CHART_WIDTH * progress;
  // Y-axis draws bottom → top
  const yAxisTop = originY - CHART_HEIGHT * progress;

  // Major ticks on X (every 5 years)
  const majorXTicks: number[] = [];
  for (let yr = X_MIN; yr <= X_MAX; yr += 5) majorXTicks.push(yr);

  // Minor ticks on X (every year)
  const minorXTicks: number[] = [];
  for (let yr = X_MIN; yr <= X_MAX; yr += 1) {
    if (yr % 5 !== 0) minorXTicks.push(yr);
  }

  // Major ticks on Y (every 25%)
  const majorYTicks: number[] = [];
  for (let v = Y_MIN; v <= Y_MAX; v += 25) majorYTicks.push(v);

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* ── Horizontal grid lines ─────────────────────────────────── */}
      {majorYTicks.map((v) => {
        const py = yToPixel(v);
        if (v === Y_MIN) return null; // skip baseline
        return (
          <line
            key={`grid-y-${v}`}
            x1={originX}
            y1={py}
            x2={xEnd}
            y2={py}
            stroke={GRID_COLOR}
            strokeOpacity={GRID_OPACITY * gridFade}
            strokeWidth={1}
            strokeDasharray="6 4"
          />
        );
      })}

      {/* ── X axis line ───────────────────────────────────────────── */}
      <line
        x1={originX}
        y1={originY}
        x2={xAxisRight}
        y2={originY}
        stroke={AXIS_COLOR}
        strokeOpacity={AXIS_OPACITY}
        strokeWidth={1}
      />

      {/* ── Y axis line ───────────────────────────────────────────── */}
      <line
        x1={originX}
        y1={originY}
        x2={originX}
        y2={yAxisTop}
        stroke={AXIS_COLOR}
        strokeOpacity={AXIS_OPACITY}
        strokeWidth={1}
      />

      {/* ── X major ticks + labels ────────────────────────────────── */}
      {majorXTicks.map((yr) => {
        const px = xToPixel(yr);
        // Only render if the axis has drawn past this point
        if (px > xAxisRight) return null;
        const tickOpacity = interpolate(
          xAxisRight,
          [px - 10, px],
          [0, 1],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
        );
        return (
          <g key={`xtick-${yr}`} opacity={tickOpacity}>
            <line
              x1={px}
              y1={originY}
              x2={px}
              y2={originY + 8}
              stroke={AXIS_COLOR}
              strokeOpacity={AXIS_OPACITY}
              strokeWidth={1}
            />
            <text
              x={px}
              y={originY + 28}
              textAnchor="middle"
              fill={LABEL_COLOR}
              fillOpacity={TICK_LABEL_OPACITY}
              fontFamily={FONT_FAMILY}
              fontSize={10}
            >
              {yr}
            </text>
          </g>
        );
      })}

      {/* ── X minor ticks ─────────────────────────────────────────── */}
      {minorXTicks.map((yr) => {
        const px = xToPixel(yr);
        if (px > xAxisRight) return null;
        const tickOpacity = interpolate(
          xAxisRight,
          [px - 10, px],
          [0, 1],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
        );
        return (
          <line
            key={`xm-${yr}`}
            x1={px}
            y1={originY}
            x2={px}
            y2={originY + 4}
            stroke={AXIS_COLOR}
            strokeOpacity={AXIS_OPACITY * tickOpacity}
            strokeWidth={1}
          />
        );
      })}

      {/* ── Y major ticks + labels ────────────────────────────────── */}
      {majorYTicks.map((v) => {
        const py = yToPixel(v);
        if (py < yAxisTop) return null;
        const tickOpacity = interpolate(
          yAxisTop,
          [py, py + 10],
          [1, 0],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
        );
        return (
          <g key={`ytick-${v}`} opacity={tickOpacity}>
            <line
              x1={originX - 6}
              y1={py}
              x2={originX}
              y2={py}
              stroke={AXIS_COLOR}
              strokeOpacity={AXIS_OPACITY}
              strokeWidth={1}
            />
            <text
              x={originX - 14}
              y={py + 4}
              textAnchor="end"
              fill={LABEL_COLOR}
              fillOpacity={TICK_LABEL_OPACITY}
              fontFamily={FONT_FAMILY}
              fontSize={10}
            >
              {v}%
            </text>
          </g>
        );
      })}

      {/* ── Axis labels ───────────────────────────────────────────── */}
      <text
        x={MARGIN_LEFT + CHART_WIDTH / 2}
        y={originY + 64}
        textAnchor="middle"
        fill={LABEL_COLOR}
        fillOpacity={LABEL_OPACITY * gridFade}
        fontFamily={FONT_FAMILY}
        fontSize={12}
      >
        Year
      </text>
      <text
        x={0}
        y={0}
        textAnchor="middle"
        fill={LABEL_COLOR}
        fillOpacity={LABEL_OPACITY * gridFade}
        fontFamily={FONT_FAMILY}
        fontSize={12}
        transform={`translate(${MARGIN_LEFT - 68}, ${MARGIN_TOP + CHART_HEIGHT / 2}) rotate(-90)`}
      >
        Cost (% of hourly wage)
      </text>
    </svg>
  );
};

export default ChartAxes;
