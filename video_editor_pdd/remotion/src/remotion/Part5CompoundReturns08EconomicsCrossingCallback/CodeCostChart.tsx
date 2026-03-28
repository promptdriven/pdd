import React from 'react';
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  GRID_COLOR,
  GRID_OPACITY,
  GRID_LINES_Y,
  GENERATE_LINE_COLOR,
  PATCH_LINE_COLOR,
  GENERATE_LINE_WIDTH,
  PATCH_LINE_WIDTH,
  DEBT_LINE_WIDTH,
  DEBT_AREA_COLOR,
  DEBT_AREA_OPACITY,
  GENERATE_LINE_DATA,
  PATCH_LINE_DATA,
  DEBT_LINE_DATA,
  DATE_MARKER_COLOR,
  DATE_MARKER_OPACITY,
  YEAR_MARKERS,
  yearToX,
  costToY,
  LABEL_DIMMED_OPACITY,
} from './constants';

interface CodeCostChartProps {
  dimOpacity: number;
}

function dataToSvgPath(data: [number, number][]): string {
  return data
    .map(([year, cost], i) => {
      const x = yearToX(year);
      const y = costToY(cost);
      return `${i === 0 ? 'M' : 'L'} ${x} ${y}`;
    })
    .join(' ');
}

function dataToAreaPath(
  upper: [number, number][],
  lower: [number, number][]
): string {
  // Forward along upper, then backward along lower
  const forwardParts = upper.map(([year, cost], i) => {
    const x = yearToX(year);
    const y = costToY(cost);
    return `${i === 0 ? 'M' : 'L'} ${x} ${y}`;
  });
  const reverseParts = [...lower].reverse().map(([year, cost]) => {
    const x = yearToX(year);
    const y = costToY(cost);
    return `L ${x} ${y}`;
  });
  return [...forwardParts, ...reverseParts, 'Z'].join(' ');
}

export const CodeCostChart: React.FC<CodeCostChartProps> = ({ dimOpacity }) => {
  const generatePath = dataToSvgPath(GENERATE_LINE_DATA);
  const patchPath = dataToSvgPath(PATCH_LINE_DATA);
  const debtPath = dataToSvgPath(DEBT_LINE_DATA);
  const debtAreaPath = dataToAreaPath(DEBT_LINE_DATA, PATCH_LINE_DATA);

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Grid lines */}
      {GRID_LINES_Y.map((y) => (
        <line
          key={y}
          x1={CHART_LEFT}
          y1={y}
          x2={CHART_RIGHT}
          y2={y}
          stroke={GRID_COLOR}
          strokeOpacity={GRID_OPACITY}
          strokeWidth={1}
        />
      ))}

      {/* Year markers on x-axis */}
      {YEAR_MARKERS.map((year) => {
        const x = yearToX(year);
        return (
          <text
            key={year}
            x={x}
            y={CHART_BOTTOM + 35}
            fill={DATE_MARKER_COLOR}
            fillOpacity={DATE_MARKER_OPACITY}
            fontSize={14}
            fontFamily="Inter, sans-serif"
            textAnchor="middle"
          >
            {year}
          </text>
        );
      })}

      {/* Shaded debt area between amber lines */}
      <path
        d={debtAreaPath}
        fill={DEBT_AREA_COLOR}
        fillOpacity={DEBT_AREA_OPACITY}
      />

      {/* Generate line (blue) — well below */}
      <path
        d={generatePath}
        stroke={GENERATE_LINE_COLOR}
        strokeWidth={GENERATE_LINE_WIDTH}
        fill="none"
        strokeLinecap="round"
        strokeLinejoin="round"
      />

      {/* Immediate patch line (amber solid) */}
      <path
        d={patchPath}
        stroke={PATCH_LINE_COLOR}
        strokeWidth={PATCH_LINE_WIDTH}
        fill="none"
        strokeLinecap="round"
        strokeLinejoin="round"
      />

      {/* Total cost with debt (amber dashed) */}
      <path
        d={debtPath}
        stroke={PATCH_LINE_COLOR}
        strokeWidth={DEBT_LINE_WIDTH}
        fill="none"
        strokeDasharray="10 6"
        strokeLinecap="round"
        strokeLinejoin="round"
      />

      {/* Legend */}
      <g opacity={dimOpacity}>
        {/* Generate legend */}
        <line
          x1={CHART_LEFT}
          y1={CHART_TOP - 40}
          x2={CHART_LEFT + 30}
          y2={CHART_TOP - 40}
          stroke={GENERATE_LINE_COLOR}
          strokeWidth={3}
        />
        <text
          x={CHART_LEFT + 40}
          y={CHART_TOP - 35}
          fill={GENERATE_LINE_COLOR}
          fontSize={14}
          fontFamily="Inter, sans-serif"
          opacity={LABEL_DIMMED_OPACITY}
        >
          Cost to generate
        </text>

        {/* Patch legend */}
        <line
          x1={CHART_LEFT + 220}
          y1={CHART_TOP - 40}
          x2={CHART_LEFT + 250}
          y2={CHART_TOP - 40}
          stroke={PATCH_LINE_COLOR}
          strokeWidth={3}
        />
        <text
          x={CHART_LEFT + 260}
          y={CHART_TOP - 35}
          fill={PATCH_LINE_COLOR}
          fontSize={14}
          fontFamily="Inter, sans-serif"
          opacity={LABEL_DIMMED_OPACITY}
        >
          Immediate patch
        </text>

        {/* Debt legend */}
        <line
          x1={CHART_LEFT + 460}
          y1={CHART_TOP - 40}
          x2={CHART_LEFT + 490}
          y2={CHART_TOP - 40}
          stroke={PATCH_LINE_COLOR}
          strokeWidth={2.5}
          strokeDasharray="10 6"
        />
        <text
          x={CHART_LEFT + 500}
          y={CHART_TOP - 35}
          fill={PATCH_LINE_COLOR}
          fontSize={14}
          fontFamily="Inter, sans-serif"
          opacity={LABEL_DIMMED_OPACITY}
        >
          Total cost with debt
        </text>
      </g>

      {/* Y-axis label */}
      <text
        x={CHART_LEFT - 20}
        y={CHART_TOP + (CHART_BOTTOM - CHART_TOP) / 2}
        fill="#64748B"
        fillOpacity={dimOpacity}
        fontSize={14}
        fontFamily="Inter, sans-serif"
        textAnchor="middle"
        transform={`rotate(-90, ${CHART_LEFT - 20}, ${CHART_TOP + (CHART_BOTTOM - CHART_TOP) / 2})`}
      >
        Relative Cost
      </text>
    </svg>
  );
};

export default CodeCostChart;
