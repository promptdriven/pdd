import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

// Chart layout constants
const CHART_LEFT = 140;
const CHART_RIGHT = 1300;
const CHART_TOP = 180;
const CHART_BOTTOM = 820;
const CHART_GRID_COLOR = 'rgba(148, 163, 184, 0.12)';
const CHART_SOLID_LINE_COLOR = '#F59E0B';
const CHART_DASHED_LINE_COLOR = '#3B82F6';
const DEBT_AREA_BASE_COLOR = 'rgba(239, 68, 68,';
const SOURCE_TEXT_COLOR = '#94A3B8';
const FONT_FAMILY = 'Inter, sans-serif';
const PULSE_START = 60;
const PULSE_CYCLE_FRAMES = 45;
const PULSE_MIN_OPACITY = 0.12;
const PULSE_MAX_OPACITY = 0.20;

const CHART_YEARS = [2020, 2021, 2022, 2023, 2024, 2025];
// Solid line: total code generation (rising fast)
const SOLID_LINE_Y = [700, 680, 640, 560, 440, 340];
// Dashed line: maintained/patched code (stays flat or rises = debt gap)
const DASHED_LINE_Y = [710, 700, 680, 680, 700, 720];

function yearToX(year: number): number {
  const ratio = (year - 2020) / (2025 - 2020);
  return CHART_LEFT + ratio * (CHART_RIGHT - CHART_LEFT);
}

function buildPolylinePoints(yValues: number[]): string {
  return yValues
    .map((y, i) => `${yearToX(CHART_YEARS[i])},${y}`)
    .join(' ');
}

function buildDebtAreaPath(solidY: number[], dashedY: number[]): string {
  // Forward along solid line (top of debt area)
  const forward = solidY
    .map((y, i) => `${yearToX(CHART_YEARS[i])},${y}`)
    .join(' L ');
  // Backward along dashed line (bottom of debt area)
  const backward = [...dashedY]
    .reverse()
    .map((y, i) => {
      const yearIdx = dashedY.length - 1 - i;
      return `${yearToX(CHART_YEARS[yearIdx])},${y}`;
    })
    .join(' L ');
  return `M ${forward} L ${backward} Z`;
}

export const ChartBackground: React.FC = () => {
  const frame = useCurrentFrame();

  // Debt area pulse: starts at frame 60, oscillates on 45-frame cycle
  let debtOpacity = PULSE_MIN_OPACITY;
  if (frame >= PULSE_START) {
    const pulseFrame = (frame - PULSE_START) % (PULSE_CYCLE_FRAMES * 2);
    if (pulseFrame < PULSE_CYCLE_FRAMES) {
      debtOpacity = interpolate(
        pulseFrame,
        [0, PULSE_CYCLE_FRAMES],
        [PULSE_MIN_OPACITY, PULSE_MAX_OPACITY],
        { easing: Easing.inOut(Easing.sin) },
      );
    } else {
      debtOpacity = interpolate(
        pulseFrame - PULSE_CYCLE_FRAMES,
        [0, PULSE_CYCLE_FRAMES],
        [PULSE_MAX_OPACITY, PULSE_MIN_OPACITY],
        { easing: Easing.inOut(Easing.sin) },
      );
    }
  }

  const debtPath = buildDebtAreaPath(SOLID_LINE_Y, DASHED_LINE_Y);

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Chart title */}
      <text
        x={CHART_LEFT}
        y={CHART_TOP - 40}
        fill="#FFFFFF"
        fontFamily={FONT_FAMILY}
        fontSize={22}
        fontWeight={700}
        opacity={0.9}
      >
        Code Generation vs. Maintenance Cost
      </text>

      {/* Grid lines */}
      {CHART_YEARS.map((year) => {
        const x = yearToX(year);
        return (
          <g key={year}>
            <line
              x1={x}
              y1={CHART_TOP}
              x2={x}
              y2={CHART_BOTTOM}
              stroke={CHART_GRID_COLOR}
              strokeWidth={1}
            />
            <text
              x={x}
              y={CHART_BOTTOM + 30}
              fill={SOURCE_TEXT_COLOR}
              fontFamily={FONT_FAMILY}
              fontSize={14}
              textAnchor="middle"
            >
              {year}
            </text>
          </g>
        );
      })}

      {/* Horizontal grid lines */}
      {[0, 1, 2, 3, 4].map((i) => {
        const y = CHART_TOP + (i / 4) * (CHART_BOTTOM - CHART_TOP);
        return (
          <line
            key={`hgrid-${i}`}
            x1={CHART_LEFT}
            y1={y}
            x2={CHART_RIGHT}
            y2={y}
            stroke={CHART_GRID_COLOR}
            strokeWidth={1}
          />
        );
      })}

      {/* Y-axis labels */}
      <text
        x={CHART_LEFT - 20}
        y={CHART_TOP + 5}
        fill={SOURCE_TEXT_COLOR}
        fontFamily={FONT_FAMILY}
        fontSize={12}
        textAnchor="end"
      >
        High
      </text>
      <text
        x={CHART_LEFT - 20}
        y={CHART_BOTTOM + 5}
        fill={SOURCE_TEXT_COLOR}
        fontFamily={FONT_FAMILY}
        fontSize={12}
        textAnchor="end"
      >
        Low
      </text>
      <text
        x={CHART_LEFT - 50}
        y={(CHART_TOP + CHART_BOTTOM) / 2}
        fill={SOURCE_TEXT_COLOR}
        fontFamily={FONT_FAMILY}
        fontSize={13}
        textAnchor="middle"
        transform={`rotate(-90, ${CHART_LEFT - 50}, ${(CHART_TOP + CHART_BOTTOM) / 2})`}
      >
        Relative Cost / Volume
      </text>

      {/* Debt shaded area (between the two lines) */}
      <path
        d={debtPath}
        fill={`${DEBT_AREA_BASE_COLOR} ${debtOpacity})`}
      />

      {/* Solid line — Code generated (amber) */}
      <polyline
        points={buildPolylinePoints(SOLID_LINE_Y)}
        fill="none"
        stroke={CHART_SOLID_LINE_COLOR}
        strokeWidth={2.5}
        strokeLinejoin="round"
      />

      {/* Dashed line — Maintenance cost (blue) */}
      <polyline
        points={buildPolylinePoints(DASHED_LINE_Y)}
        fill="none"
        stroke={CHART_DASHED_LINE_COLOR}
        strokeWidth={2}
        strokeDasharray="8 4"
        strokeLinejoin="round"
      />

      {/* Legend */}
      <g transform="translate(200, 870)">
        <line x1={0} y1={0} x2={30} y2={0} stroke={CHART_SOLID_LINE_COLOR} strokeWidth={2.5} />
        <text x={38} y={4} fill={SOURCE_TEXT_COLOR} fontFamily={FONT_FAMILY} fontSize={13}>
          Code generated
        </text>
        <line x1={200} y1={0} x2={230} y2={0} stroke={CHART_DASHED_LINE_COLOR} strokeWidth={2} strokeDasharray="8 4" />
        <text x={238} y={4} fill={SOURCE_TEXT_COLOR} fontFamily={FONT_FAMILY} fontSize={13}>
          Maintenance / patching cost
        </text>
      </g>

      {/* "AI assistants arrive" marker */}
      <line
        x1={yearToX(2023)}
        y1={CHART_TOP}
        x2={yearToX(2023)}
        y2={CHART_BOTTOM}
        stroke="rgba(239, 68, 68, 0.3)"
        strokeWidth={1.5}
        strokeDasharray="4 3"
      />
      <text
        x={yearToX(2023) + 6}
        y={CHART_TOP + 20}
        fill="#EF4444"
        fontFamily={FONT_FAMILY}
        fontSize={11}
        opacity={0.7}
      >
        AI assistants arrive
      </text>
    </svg>
  );
};

export default ChartBackground;
