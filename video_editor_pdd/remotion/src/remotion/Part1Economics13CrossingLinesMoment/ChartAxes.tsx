// ChartAxes.tsx — Renders the chart grid, axes, tick labels, and legend
import React from 'react';
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  CHART_WIDTH,
  AXIS_COLOR,
  AXIS_LABEL_COLOR,
  GRID_COLOR,
  FONT_FAMILY,
  AXIS_FONT_SIZE,
  TITLE_FONT_SIZE,
  Y_AXIS_TICKS,
  X_AXIS_TICKS,
  COST_MIN,
  COST_MAX,
  YEAR_MIN,
  YEAR_MAX,
  LEGEND_ITEMS,
  yearToX,
  costToY,
} from './constants';

export const ChartAxes: React.FC = () => {
  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Grid lines — horizontal */}
      {Y_AXIS_TICKS.map((tick) => {
        const y = costToY(tick);
        return (
          <line
            key={`grid-h-${tick}`}
            x1={CHART_LEFT}
            y1={y}
            x2={CHART_RIGHT}
            y2={y}
            stroke={GRID_COLOR}
            strokeWidth={1}
          />
        );
      })}

      {/* Grid lines — vertical */}
      {X_AXIS_TICKS.map((tick) => {
        const x = yearToX(tick);
        return (
          <line
            key={`grid-v-${tick}`}
            x1={x}
            y1={CHART_TOP}
            x2={x}
            y2={CHART_BOTTOM}
            stroke={GRID_COLOR}
            strokeWidth={1}
          />
        );
      })}

      {/* X-axis */}
      <line
        x1={CHART_LEFT}
        y1={CHART_BOTTOM}
        x2={CHART_RIGHT}
        y2={CHART_BOTTOM}
        stroke={AXIS_COLOR}
        strokeWidth={2}
      />

      {/* Y-axis */}
      <line
        x1={CHART_LEFT}
        y1={CHART_TOP}
        x2={CHART_LEFT}
        y2={CHART_BOTTOM}
        stroke={AXIS_COLOR}
        strokeWidth={2}
      />

      {/* Y-axis tick labels */}
      {Y_AXIS_TICKS.map((tick) => {
        const y = costToY(tick);
        return (
          <text
            key={`y-label-${tick}`}
            x={CHART_LEFT - 16}
            y={y + 5}
            textAnchor="end"
            fill={AXIS_LABEL_COLOR}
            fontFamily={FONT_FAMILY}
            fontSize={AXIS_FONT_SIZE}
          >
            {tick}
          </text>
        );
      })}

      {/* X-axis tick labels */}
      {X_AXIS_TICKS.map((tick) => {
        const x = yearToX(tick);
        return (
          <text
            key={`x-label-${tick}`}
            x={x}
            y={CHART_BOTTOM + 30}
            textAnchor="middle"
            fill={AXIS_LABEL_COLOR}
            fontFamily={FONT_FAMILY}
            fontSize={AXIS_FONT_SIZE}
          >
            {tick}
          </text>
        );
      })}

      {/* Y-axis label */}
      <text
        x={50}
        y={CHART_TOP + (CHART_BOTTOM - CHART_TOP) / 2}
        textAnchor="middle"
        fill={AXIS_LABEL_COLOR}
        fontFamily={FONT_FAMILY}
        fontSize={AXIS_FONT_SIZE}
        transform={`rotate(-90, 50, ${CHART_TOP + (CHART_BOTTOM - CHART_TOP) / 2})`}
      >
        Relative Cost
      </text>

      {/* X-axis label */}
      <text
        x={CHART_LEFT + CHART_WIDTH / 2}
        y={CHART_BOTTOM + 60}
        textAnchor="middle"
        fill={AXIS_LABEL_COLOR}
        fontFamily={FONT_FAMILY}
        fontSize={AXIS_FONT_SIZE}
      >
        Year
      </text>

      {/* Chart title */}
      <text
        x={CHART_LEFT + CHART_WIDTH / 2}
        y={CHART_TOP - 40}
        textAnchor="middle"
        fill="#E2E8F0"
        fontFamily={FONT_FAMILY}
        fontSize={TITLE_FONT_SIZE}
        fontWeight={600}
      >
        Code Cost: Generate vs. Patch
      </text>

      {/* Legend */}
      {LEGEND_ITEMS.map((item, i) => {
        const lx = CHART_RIGHT - 280;
        const ly = CHART_TOP + 20 + i * 28;
        return (
          <g key={`legend-${i}`}>
            <line
              x1={lx}
              y1={ly}
              x2={lx + 30}
              y2={ly}
              stroke={item.color}
              strokeWidth={item.dashed ? 2 : 3}
              strokeDasharray={item.dashed ? '8,4' : 'none'}
            />
            <text
              x={lx + 40}
              y={ly + 5}
              fill={AXIS_LABEL_COLOR}
              fontFamily={FONT_FAMILY}
              fontSize={13}
            >
              {item.label}
            </text>
          </g>
        );
      })}
    </svg>
  );
};

export default ChartAxes;
