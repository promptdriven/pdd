import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

// ─── Chart constants (inlined to avoid cross-file imports) ─────────
const CHART_LEFT = 120;
const CHART_RIGHT = 1300;
const CHART_TOP = 160;
const CHART_BOTTOM = 820;
const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;
const CHART_YEARS = [2020, 2021, 2022, 2023, 2024, 2025] as const;

const COLOR_LINE_SOLID = '#3B82F6';
const COLOR_LINE_DASHED = '#F59E0B';
const COLOR_DEBT_FILL = '#F59E0B';
const COLOR_SLATE = '#94A3B8';
const COLOR_WHITE = '#FFFFFF';
const BG_COLOR = '#0A0F1A';

const FONT_FAMILY = 'Inter, system-ui, sans-serif';
const FONT_AXIS_SIZE = 13;
const FONT_TITLE_SIZE = 22;

const PULSE_START = 60;
const PULSE_MIN_OPACITY = 0.12;
const PULSE_MAX_OPACITY = 0.20;
const PULSE_CYCLE_FRAMES = 45;

// ─── Synthetic chart data ──────────────────────────────────────────
// Solid line = actual code cost (rising sharply after 2023)
const solidLineY = [0.65, 0.60, 0.55, 0.42, 0.28, 0.18]; // fraction from top (lower = higher cost)
// Dashed line = expected/ideal trajectory
const dashedLineY = [0.65, 0.62, 0.58, 0.52, 0.48, 0.44];

function yearToX(index: number): number {
  return CHART_LEFT + (index / (CHART_YEARS.length - 1)) * CHART_WIDTH;
}

function fractionToY(f: number): number {
  return CHART_TOP + f * CHART_HEIGHT;
}

function buildPolylinePoints(yFractions: number[]): string {
  return yFractions.map((f, i) => `${yearToX(i)},${fractionToY(f)}`).join(' ');
}

function buildDebtAreaPath(solidY: number[], dashedY: number[]): string {
  // Area between dashed (top/ideal) and solid (bottom/actual) from year 2022 onward (index 2)
  const startIdx = 2;
  const forwardPoints = solidY
    .slice(startIdx)
    .map((f, i) => `${yearToX(i + startIdx)},${fractionToY(f)}`)
    .join(' L');
  const backwardPoints = dashedY
    .slice(startIdx)
    .reverse()
    .map((f, i) => {
      const yearIdx = dashedY.length - 1 - i;
      if (yearIdx < startIdx) return null;
      return `${yearToX(yearIdx)},${fractionToY(f)}`;
    })
    .filter(Boolean)
    .join(' L');
  return `M${forwardPoints} L${backwardPoints} Z`;
}

export const DebtAreaChart: React.FC = () => {
  const frame = useCurrentFrame();

  // Debt area pulse
  const pulseFrame = Math.max(0, frame - PULSE_START);
  const cyclePosition = (pulseFrame % PULSE_CYCLE_FRAMES) / PULSE_CYCLE_FRAMES;
  const pulseOpacity =
    frame < PULSE_START
      ? PULSE_MIN_OPACITY
      : interpolate(
          Math.sin(cyclePosition * Math.PI * 2),
          [-1, 1],
          [PULSE_MIN_OPACITY, PULSE_MAX_OPACITY],
        );

  const solidPoints = buildPolylinePoints(solidLineY);
  const dashedPoints = buildPolylinePoints(dashedLineY);
  const debtPath = buildDebtAreaPath(solidLineY, dashedLineY);

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: 1920,
        height: 1080,
      }}
    >
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', left: 0, top: 0 }}
      >
        {/* Chart title */}
        <text
          x={CHART_LEFT}
          y={CHART_TOP - 40}
          fill={COLOR_WHITE}
          fontFamily={FONT_FAMILY}
          fontSize={FONT_TITLE_SIZE}
          fontWeight={700}
        >
          Code Generation vs. Maintenance Cost
        </text>

        {/* Grid lines */}
        {[0, 0.25, 0.5, 0.75, 1].map((f) => (
          <line
            key={f}
            x1={CHART_LEFT}
            y1={fractionToY(f)}
            x2={CHART_RIGHT}
            y2={fractionToY(f)}
            stroke={COLOR_SLATE}
            strokeOpacity={0.15}
            strokeWidth={1}
          />
        ))}

        {/* Vertical grid lines at each year */}
        {CHART_YEARS.map((_, i) => (
          <line
            key={i}
            x1={yearToX(i)}
            y1={CHART_TOP}
            x2={yearToX(i)}
            y2={CHART_BOTTOM}
            stroke={COLOR_SLATE}
            strokeOpacity={0.1}
            strokeWidth={1}
          />
        ))}

        {/* Year labels */}
        {CHART_YEARS.map((year, i) => (
          <text
            key={year}
            x={yearToX(i)}
            y={CHART_BOTTOM + 30}
            fill={COLOR_SLATE}
            fontFamily={FONT_FAMILY}
            fontSize={FONT_AXIS_SIZE}
            textAnchor="middle"
          >
            {year}
          </text>
        ))}

        {/* Y-axis labels */}
        {['High', 'Med', 'Low'].map((label, i) => (
          <text
            key={label}
            x={CHART_LEFT - 16}
            y={fractionToY(i * 0.5) + 4}
            fill={COLOR_SLATE}
            fontFamily={FONT_FAMILY}
            fontSize={FONT_AXIS_SIZE}
            textAnchor="end"
          >
            {label}
          </text>
        ))}

        {/* AI assistant arrival marker */}
        <line
          x1={yearToX(3)}
          y1={CHART_TOP}
          x2={yearToX(3)}
          y2={CHART_BOTTOM}
          stroke={COLOR_WHITE}
          strokeOpacity={0.25}
          strokeWidth={1}
          strokeDasharray="6,4"
        />
        <text
          x={yearToX(3)}
          y={CHART_TOP - 10}
          fill={COLOR_SLATE}
          fontFamily={FONT_FAMILY}
          fontSize={11}
          textAnchor="middle"
        >
          AI assistants arrive
        </text>

        {/* Debt shaded area (between the two lines) */}
        <path
          d={debtPath}
          fill={COLOR_DEBT_FILL}
          opacity={pulseOpacity}
        />

        {/* Dashed line (expected/ideal) */}
        <polyline
          points={dashedPoints}
          fill="none"
          stroke={COLOR_LINE_DASHED}
          strokeWidth={2.5}
          strokeDasharray="8,5"
          opacity={0.8}
        />

        {/* Solid line (actual cost) */}
        <polyline
          points={solidPoints}
          fill="none"
          stroke={COLOR_LINE_SOLID}
          strokeWidth={2.5}
          opacity={0.9}
        />

        {/* Data points on solid line */}
        {solidLineY.map((f, i) => (
          <circle
            key={`s-${i}`}
            cx={yearToX(i)}
            cy={fractionToY(f)}
            r={4}
            fill={COLOR_LINE_SOLID}
            stroke={BG_COLOR}
            strokeWidth={2}
          />
        ))}

        {/* Data points on dashed line */}
        {dashedLineY.map((f, i) => (
          <circle
            key={`d-${i}`}
            cx={yearToX(i)}
            cy={fractionToY(f)}
            r={4}
            fill={COLOR_LINE_DASHED}
            stroke={BG_COLOR}
            strokeWidth={2}
          />
        ))}

        {/* Legend */}
        <line x1={CHART_LEFT} y1={CHART_BOTTOM + 56} x2={CHART_LEFT + 30} y2={CHART_BOTTOM + 56} stroke={COLOR_LINE_SOLID} strokeWidth={2.5} />
        <text x={CHART_LEFT + 38} y={CHART_BOTTOM + 60} fill={COLOR_SLATE} fontFamily={FONT_FAMILY} fontSize={12}>
          Actual cost trajectory
        </text>

        <line x1={CHART_LEFT + 240} y1={CHART_BOTTOM + 56} x2={CHART_LEFT + 270} y2={CHART_BOTTOM + 56} stroke={COLOR_LINE_DASHED} strokeWidth={2.5} strokeDasharray="8,5" />
        <text x={CHART_LEFT + 278} y={CHART_BOTTOM + 60} fill={COLOR_SLATE} fontFamily={FONT_FAMILY} fontSize={12}>
          Expected trajectory
        </text>

        <rect x={CHART_LEFT + 480} y={CHART_BOTTOM + 48} width={16} height={16} fill={COLOR_DEBT_FILL} opacity={0.16} rx={2} />
        <text x={CHART_LEFT + 504} y={CHART_BOTTOM + 60} fill={COLOR_SLATE} fontFamily={FONT_FAMILY} fontSize={12}>
          Technical debt area
        </text>
      </svg>
    </div>
  );
};

export default DebtAreaChart;
