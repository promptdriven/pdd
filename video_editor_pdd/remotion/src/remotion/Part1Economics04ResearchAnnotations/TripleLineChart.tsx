import React from 'react';
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  YEARS,
  IMMEDIATE_COST_DATA,
  TOTAL_COST_DATA,
  GREEN,
  AMBER,
  MUTED,
  WHITE,
  Y_AXIS_LABEL,
  CHART_TITLE,
} from './constants';

/**
 * Static triple-line chart that represents the base chart from the
 * previous spec (03_code_cost_triple_line). This renders immediately
 * at frame 0 as a continuation.
 */

// Map data values (0-1) to chart Y coordinates (inverted: 0=bottom, 1=top)
const valueToY = (v: number): number => {
  return CHART_BOTTOM - v * CHART_HEIGHT;
};

// Map year index to chart X coordinate
const indexToX = (i: number): number => {
  return CHART_LEFT + (i / (YEARS.length - 1)) * CHART_WIDTH;
};

// Build SVG path from data points
const buildPath = (data: number[]): string => {
  return data
    .map((v, i) => {
      const x = indexToX(i);
      const y = valueToY(v);
      return `${i === 0 ? 'M' : 'L'} ${x} ${y}`;
    })
    .join(' ');
};

// Build the shaded area between two lines (debt area)
const buildAreaPath = (
  upper: number[],
  lower: number[],
): string => {
  // Go forward along upper, then backward along lower
  const forwardPoints = upper.map((v, i) => `${indexToX(i)} ${valueToY(v)}`);
  const backwardPoints = [...lower]
    .map((v, i) => `${indexToX(i)} ${valueToY(v)}`)
    .reverse();

  return `M ${forwardPoints.join(' L ')} L ${backwardPoints.join(' L ')} Z`;
};

const TripleLineChart: React.FC = () => {
  const immediatePath = buildPath(IMMEDIATE_COST_DATA);
  const totalPath = buildPath(TOTAL_COST_DATA);
  const debtAreaPath = buildAreaPath(TOTAL_COST_DATA, IMMEDIATE_COST_DATA);

  // Y-axis tick values
  const yTicks = [0, 0.25, 0.5, 0.75, 1.0];

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: '100%',
        height: '100%',
      }}
    >
      {/* Chart title */}
      <div
        style={{
          position: 'absolute',
          left: CHART_LEFT,
          top: 50,
          fontFamily: 'Inter, sans-serif',
          fontSize: 22,
          fontWeight: 700,
          color: WHITE,
          opacity: 0.9,
        }}
      >
        {CHART_TITLE}
      </div>

      <svg
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: '100%',
          height: '100%',
        }}
      >
        {/* Grid lines */}
        {yTicks.map((tick) => (
          <line
            key={tick}
            x1={CHART_LEFT}
            y1={valueToY(tick)}
            x2={CHART_RIGHT}
            y2={valueToY(tick)}
            stroke={MUTED}
            strokeWidth={0.5}
            opacity={0.1}
          />
        ))}

        {/* Y-axis labels */}
        {yTicks.map((tick) => (
          <text
            key={`label-${tick}`}
            x={CHART_LEFT - 16}
            y={valueToY(tick) + 4}
            fill={MUTED}
            fontSize={10}
            fontFamily="Inter, sans-serif"
            textAnchor="end"
            opacity={0.35}
          >
            {`${Math.round(tick * 100)}%`}
          </text>
        ))}

        {/* X-axis labels */}
        {YEARS.map((year, i) => (
          <text
            key={year}
            x={indexToX(i)}
            y={CHART_BOTTOM + 30}
            fill={MUTED}
            fontSize={11}
            fontFamily="Inter, sans-serif"
            textAnchor="middle"
            opacity={0.4}
          >
            {year}
          </text>
        ))}

        {/* Y-axis label */}
        <text
          x={50}
          y={CHART_TOP + CHART_HEIGHT / 2}
          fill={MUTED}
          fontSize={11}
          fontFamily="Inter, sans-serif"
          textAnchor="middle"
          opacity={0.35}
          transform={`rotate(-90, 50, ${CHART_TOP + CHART_HEIGHT / 2})`}
        >
          {Y_AXIS_LABEL}
        </text>

        {/* Axes */}
        <line
          x1={CHART_LEFT}
          y1={CHART_TOP}
          x2={CHART_LEFT}
          y2={CHART_BOTTOM}
          stroke={MUTED}
          strokeWidth={1}
          opacity={0.2}
        />
        <line
          x1={CHART_LEFT}
          y1={CHART_BOTTOM}
          x2={CHART_RIGHT}
          y2={CHART_BOTTOM}
          stroke={MUTED}
          strokeWidth={1}
          opacity={0.2}
        />

        {/* Debt shaded area (between total cost and immediate cost) */}
        <path
          d={debtAreaPath}
          fill={AMBER}
          opacity={0.08}
        />

        {/* Line 1: Immediate patch cost (solid green, dropping) */}
        <path
          d={immediatePath}
          fill="none"
          stroke={GREEN}
          strokeWidth={2.5}
          opacity={0.85}
        />

        {/* Line 2: Total cost with debt (dashed amber, flat/rising) */}
        <path
          d={totalPath}
          fill="none"
          stroke={AMBER}
          strokeWidth={2.5}
          strokeDasharray="8 4"
          opacity={0.85}
        />

        {/* Data points - Immediate cost */}
        {IMMEDIATE_COST_DATA.map((v, i) => (
          <circle
            key={`imm-${i}`}
            cx={indexToX(i)}
            cy={valueToY(v)}
            r={3}
            fill={GREEN}
            opacity={0.7}
          />
        ))}

        {/* Data points - Total cost */}
        {TOTAL_COST_DATA.map((v, i) => (
          <circle
            key={`tot-${i}`}
            cx={indexToX(i)}
            cy={valueToY(v)}
            r={3}
            fill={AMBER}
            opacity={0.7}
          />
        ))}
      </svg>

      {/* Legend */}
      <div
        style={{
          position: 'absolute',
          left: CHART_LEFT + 20,
          top: CHART_TOP + 10,
          display: 'flex',
          gap: 24,
        }}
      >
        <div style={{ display: 'flex', alignItems: 'center', gap: 8 }}>
          <div
            style={{
              width: 24,
              height: 2.5,
              backgroundColor: GREEN,
              borderRadius: 1,
            }}
          />
          <span
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 10,
              color: MUTED,
              opacity: 0.5,
            }}
          >
            Immediate Patch Cost
          </span>
        </div>
        <div style={{ display: 'flex', alignItems: 'center', gap: 8 }}>
          <div
            style={{
              width: 24,
              height: 0,
              borderTop: `2.5px dashed ${AMBER}`,
            }}
          />
          <span
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 10,
              color: MUTED,
              opacity: 0.5,
            }}
          >
            Total Cost (incl. Debt)
          </span>
        </div>
      </div>
    </div>
  );
};

export default TripleLineChart;

// Export helper for annotation target points
export const getTargetPoint = (
  series: 'immediate' | 'total' | 'debtArea',
  yearIndex: number,
): { x: number; y: number } => {
  const data = series === 'immediate' ? IMMEDIATE_COST_DATA : TOTAL_COST_DATA;

  if (series === 'debtArea') {
    // Center of the debt area at the given year index
    const midValue =
      (TOTAL_COST_DATA[yearIndex] + IMMEDIATE_COST_DATA[yearIndex]) / 2;
    return { x: indexToX(yearIndex), y: valueToY(midValue) };
  }

  return { x: indexToX(yearIndex), y: valueToY(data[yearIndex]) };
};
