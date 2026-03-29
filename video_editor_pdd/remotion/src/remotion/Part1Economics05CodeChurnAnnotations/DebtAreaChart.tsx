import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

// ── Local constants (mirrors constants.ts but self-contained) ───
const CHART_LEFT = 140;
const CHART_TOP = 120;
const CHART_WIDTH = 1100;
const CHART_HEIGHT = 600;

const YEAR_START = 2019;
const YEAR_END = 2025;

const COLOR_AXIS_LINE = "#334155";
const COLOR_AXIS_LABEL = "#64748B";
const COLOR_CHART_SOLID = "#F59E0B";
const COLOR_CHART_DASHED = "#F59E0B";
const COLOR_CHART_DEBT_FILL = "#F59E0B";

const DEBT_PULSE_START = 60;
const DEBT_PULSE_CYCLE = 45;
const DEBT_PULSE_MIN = 0.12;
const DEBT_PULSE_MAX = 0.20;

const SOLID_LINE_POINTS: [number, number][] = [
  [2019, 0.18],
  [2020, 0.22],
  [2021, 0.30],
  [2022, 0.38],
  [2023, 0.55],
  [2024, 0.75],
  [2025, 0.90],
];

const DASHED_LINE_POINTS: [number, number][] = [
  [2019, 0.16],
  [2020, 0.19],
  [2021, 0.24],
  [2022, 0.28],
  [2023, 0.30],
  [2024, 0.32],
  [2025, 0.34],
];

// ── Helpers ─────────────────────────────────────────────────────
function yearToX(year: number): number {
  return CHART_LEFT + ((year - YEAR_START) / (YEAR_END - YEAR_START)) * CHART_WIDTH;
}

function valToY(v: number): number {
  return CHART_TOP + CHART_HEIGHT - v * CHART_HEIGHT;
}

function pointsToSvgPath(pts: [number, number][]): string {
  return pts
    .map(([year, val], i) => `${i === 0 ? "M" : "L"} ${yearToX(year)} ${valToY(val)}`)
    .join(" ");
}

function buildDebtAreaPath(
  solidPts: [number, number][],
  dashedPts: [number, number][]
): string {
  // Forward along solid line, then back along dashed line (reversed)
  const forward = solidPts.map(([y, v]) => `${yearToX(y)},${valToY(v)}`);
  const backward = [...dashedPts].reverse().map(([y, v]) => `${yearToX(y)},${valToY(v)}`);
  return `M ${forward.join(" L ")} L ${backward.join(" L ")} Z`;
}

// ── Component ───────────────────────────────────────────────────
export const DebtAreaChart: React.FC = () => {
  const frame = useCurrentFrame();

  // Debt area pulsing opacity
  const pulsing = frame >= DEBT_PULSE_START;
  let debtOpacity = DEBT_PULSE_MIN;
  if (pulsing) {
    const cycleFrame = (frame - DEBT_PULSE_START) % DEBT_PULSE_CYCLE;
    const halfCycle = DEBT_PULSE_CYCLE / 2;
    if (cycleFrame <= halfCycle) {
      debtOpacity = interpolate(cycleFrame, [0, halfCycle], [DEBT_PULSE_MIN, DEBT_PULSE_MAX], {
        easing: Easing.inOut(Easing.sin),
      });
    } else {
      debtOpacity = interpolate(
        cycleFrame,
        [halfCycle, DEBT_PULSE_CYCLE],
        [DEBT_PULSE_MAX, DEBT_PULSE_MIN],
        { easing: Easing.inOut(Easing.sin) }
      );
    }
  }

  const solidPath = pointsToSvgPath(SOLID_LINE_POINTS);
  const dashedPath = pointsToSvgPath(DASHED_LINE_POINTS);
  const debtArea = buildDebtAreaPath(SOLID_LINE_POINTS, DASHED_LINE_POINTS);

  const years = [2019, 2020, 2021, 2022, 2023, 2024, 2025];

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Y-axis */}
      <line
        x1={CHART_LEFT}
        y1={CHART_TOP}
        x2={CHART_LEFT}
        y2={CHART_TOP + CHART_HEIGHT}
        stroke={COLOR_AXIS_LINE}
        strokeWidth={2}
      />
      {/* X-axis */}
      <line
        x1={CHART_LEFT}
        y1={CHART_TOP + CHART_HEIGHT}
        x2={CHART_LEFT + CHART_WIDTH}
        y2={CHART_TOP + CHART_HEIGHT}
        stroke={COLOR_AXIS_LINE}
        strokeWidth={2}
      />

      {/* X-axis year labels */}
      {years.map((yr) => (
        <text
          key={yr}
          x={yearToX(yr)}
          y={CHART_TOP + CHART_HEIGHT + 30}
          textAnchor="middle"
          fill={COLOR_AXIS_LABEL}
          fontSize={14}
          fontFamily="Inter, sans-serif"
        >
          {yr}
        </text>
      ))}

      {/* Y-axis label */}
      <text
        x={CHART_LEFT - 60}
        y={CHART_TOP + CHART_HEIGHT / 2}
        textAnchor="middle"
        fill={COLOR_AXIS_LABEL}
        fontSize={13}
        fontFamily="Inter, sans-serif"
        transform={`rotate(-90, ${CHART_LEFT - 60}, ${CHART_TOP + CHART_HEIGHT / 2})`}
      >
        Relative Code Cost
      </text>

      {/* Chart title */}
      <text
        x={CHART_LEFT + CHART_WIDTH / 2}
        y={CHART_TOP - 40}
        textAnchor="middle"
        fill="#E2E8F0"
        fontSize={20}
        fontWeight={600}
        fontFamily="Inter, sans-serif"
      >
        Code Generation vs. Maintenance Cost
      </text>

      {/* Debt shaded area */}
      <path d={debtArea} fill={COLOR_CHART_DEBT_FILL} opacity={debtOpacity} />

      {/* Solid line (generation cost) */}
      <path
        d={solidPath}
        fill="none"
        stroke={COLOR_CHART_SOLID}
        strokeWidth={2.5}
        opacity={0.9}
      />

      {/* Dashed line (maintenance cost) */}
      <path
        d={dashedPath}
        fill="none"
        stroke={COLOR_CHART_DASHED}
        strokeWidth={2}
        strokeDasharray="8 4"
        opacity={0.7}
      />

      {/* Legend */}
      <line
        x1={CHART_LEFT + 20}
        y1={CHART_TOP + 20}
        x2={CHART_LEFT + 50}
        y2={CHART_TOP + 20}
        stroke={COLOR_CHART_SOLID}
        strokeWidth={2.5}
      />
      <text
        x={CHART_LEFT + 58}
        y={CHART_TOP + 25}
        fill="#CBD5E1"
        fontSize={13}
        fontFamily="Inter, sans-serif"
      >
        Generated code volume
      </text>

      <line
        x1={CHART_LEFT + 20}
        y1={CHART_TOP + 44}
        x2={CHART_LEFT + 50}
        y2={CHART_TOP + 44}
        stroke={COLOR_CHART_DASHED}
        strokeWidth={2}
        strokeDasharray="8 4"
      />
      <text
        x={CHART_LEFT + 58}
        y={CHART_TOP + 49}
        fill="#CBD5E1"
        fontSize={13}
        fontFamily="Inter, sans-serif"
      >
        Maintained / patched code
      </text>

      {/* "Debt" label inside the shaded area */}
      <text
        x={yearToX(2023.5)}
        y={valToY(0.42)}
        textAnchor="middle"
        fill="#FCD34D"
        fontSize={15}
        fontWeight={600}
        fontFamily="Inter, sans-serif"
        opacity={0.65}
      >
        Technical Debt
      </text>
    </svg>
  );
};

export default DebtAreaChart;
