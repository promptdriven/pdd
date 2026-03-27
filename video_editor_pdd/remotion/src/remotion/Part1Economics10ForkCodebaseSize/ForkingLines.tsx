import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  GENERATE_LINE_DATA,
  PATCH_LINE_DATA,
  SMALL_CODEBASE_DATA,
  LARGE_CODEBASE_DATA,
  GENERATE_LINE_COLOR,
  PATCH_LINE_COLOR,
  SMALL_CODEBASE_COLOR,
  LARGE_CODEBASE_COLOR,
  MAIN_LINE_WIDTH,
  FONT_FAMILY,
  PHASE_FORK_START,
  FORK_DURATION,
  PHASE_DIVERGE_END,
} from "./constants";
import { xToPixel, yToPixel } from "./ChartAxes";

interface DataPoint {
  x: number;
  y: number;
}

/** Convert an array of data points to an SVG polyline "points" string. */
const toPolylinePoints = (data: DataPoint[]): string =>
  data.map((d) => `${xToPixel(d.x)},${yToPixel(d.y)}`).join(" ");

/**
 * Interpolate along a polyline at parameter t ∈ [0, 1].
 * Returns the subset of points up to t, with the last point interpolated.
 */
const getPartialPath = (data: DataPoint[], t: number): string => {
  if (t <= 0) return `${xToPixel(data[0].x)},${yToPixel(data[0].y)}`;
  if (t >= 1) return toPolylinePoints(data);

  const totalSegments = data.length - 1;
  const rawIdx = t * totalSegments;
  const segIdx = Math.floor(rawIdx);
  const segT = rawIdx - segIdx;

  const points: string[] = [];
  for (let i = 0; i <= segIdx; i++) {
    points.push(`${xToPixel(data[i].x)},${yToPixel(data[i].y)}`);
  }

  if (segIdx < totalSegments) {
    const a = data[segIdx];
    const b = data[segIdx + 1];
    const ix = a.x + (b.x - a.x) * segT;
    const iy = a.y + (b.y - a.y) * segT;
    points.push(`${xToPixel(ix)},${yToPixel(iy)}`);
  }

  return points.join(" ");
};

/** Get the endpoint pixel coords at parameter t along a polyline. */
const getPointAtT = (
  data: DataPoint[],
  t: number
): { px: number; py: number } => {
  const clamped = Math.max(0, Math.min(1, t));
  const totalSegments = data.length - 1;
  const rawIdx = clamped * totalSegments;
  const segIdx = Math.min(Math.floor(rawIdx), totalSegments - 1);
  const segT = rawIdx - segIdx;

  const a = data[segIdx];
  const b = data[Math.min(segIdx + 1, data.length - 1)];
  return {
    px: xToPixel(a.x + (b.x - a.x) * segT),
    py: yToPixel(a.y + (b.y - a.y) * segT),
  };
};

const ForkingLines: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Base chart lines fade in ──────────────────────────
  const baseOpacity = interpolate(frame, [0, 60], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // ── Debt shaded area (between generate line and patch/large line) ──
  const generatePoints = GENERATE_LINE_DATA.map(
    (d) => `${xToPixel(d.x)},${yToPixel(d.y)}`
  );
  const patchReversed = [...PATCH_LINE_DATA].reverse().map(
    (d) => `${xToPixel(d.x)},${yToPixel(d.y)}`
  );
  const debtAreaPoints = [...generatePoints, ...patchReversed].join(" ");

  // ── Fork animation progress ───────────────────────────
  // The fork begins at PHASE_FORK_START and completes drawing over FORK_DURATION
  // Then continues diverging until PHASE_DIVERGE_END
  const forkDrawT = interpolate(
    frame,
    [PHASE_FORK_START, PHASE_FORK_START + FORK_DURATION],
    [0, 0.5],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  const forkDivergeT = interpolate(
    frame,
    [PHASE_FORK_START + FORK_DURATION, PHASE_DIVERGE_END],
    [0.5, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  const forkT = frame < PHASE_FORK_START
    ? 0
    : frame <= PHASE_FORK_START + FORK_DURATION
      ? forkDrawT
      : forkDivergeT;

  const showForks = frame >= PHASE_FORK_START;

  // ── Fork label positions ──────────────────────────────
  const smallEndpoint = getPointAtT(SMALL_CODEBASE_DATA, forkT);
  const largeEndpoint = getPointAtT(LARGE_CODEBASE_DATA, forkT);

  const forkLabelOpacity = interpolate(
    frame,
    [PHASE_FORK_START + 30, PHASE_FORK_START + 60],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* ── Debt shaded area (pre-fork) ────────────── */}
      <polygon
        points={debtAreaPoints}
        fill="#F59E0B"
        fillOpacity={0.08 * baseOpacity}
      />

      {/* ── Generate line (blue) ─────────────────── */}
      <polyline
        points={toPolylinePoints(GENERATE_LINE_DATA)}
        fill="none"
        stroke={GENERATE_LINE_COLOR}
        strokeWidth={MAIN_LINE_WIDTH}
        opacity={baseOpacity}
      />
      {/* Generate line label */}
      <text
        x={xToPixel(2026) + 10}
        y={yToPixel(0.015)}
        fill={GENERATE_LINE_COLOR}
        fontFamily={FONT_FAMILY}
        fontSize={18}
        fontWeight={600}
        opacity={baseOpacity}
      >
        Generate (from scratch)
      </text>

      {/* ── Pre-fork patch line (amber) ──────────── */}
      <polyline
        points={toPolylinePoints(PATCH_LINE_DATA)}
        fill="none"
        stroke={PATCH_LINE_COLOR}
        strokeWidth={MAIN_LINE_WIDTH}
        opacity={baseOpacity}
      />
      {/* Patch line label (pre-fork) */}
      {!showForks && (
        <text
          x={xToPixel(2020) + 10}
          y={yToPixel(0.48) - 14}
          fill={PATCH_LINE_COLOR}
          fontFamily={FONT_FAMILY}
          fontSize={18}
          fontWeight={600}
          opacity={baseOpacity}
        >
          Patch (AI-assisted)
        </text>
      )}

      {/* ── Fork: Small codebase (green, drops) ──── */}
      {showForks && (
        <>
          <polyline
            points={getPartialPath(SMALL_CODEBASE_DATA, forkT)}
            fill="none"
            stroke={SMALL_CODEBASE_COLOR}
            strokeWidth={MAIN_LINE_WIDTH}
            strokeLinecap="round"
          />
          {/* Dot at endpoint */}
          <circle
            cx={smallEndpoint.px}
            cy={smallEndpoint.py}
            r={4}
            fill={SMALL_CODEBASE_COLOR}
            opacity={forkLabelOpacity}
          />
        </>
      )}

      {/* ── Fork: Large codebase (red, stays flat) ─ */}
      {showForks && (
        <>
          <polyline
            points={getPartialPath(LARGE_CODEBASE_DATA, forkT)}
            fill="none"
            stroke={LARGE_CODEBASE_COLOR}
            strokeWidth={MAIN_LINE_WIDTH}
            strokeLinecap="round"
          />
          {/* Dot at endpoint */}
          <circle
            cx={largeEndpoint.px}
            cy={largeEndpoint.py}
            r={4}
            fill={LARGE_CODEBASE_COLOR}
            opacity={forkLabelOpacity}
          />
        </>
      )}

      {/* ── Fork point marker ────────────────────── */}
      {showForks && (
        <circle
          cx={xToPixel(2020)}
          cy={yToPixel(0.48)}
          r={5}
          fill="#FFF"
          fillOpacity={0.9}
          stroke={PATCH_LINE_COLOR}
          strokeWidth={2}
        />
      )}

      {/* ── Fork labels ──────────────────────────── */}
      {showForks && forkT > 0.2 && (
        <>
          <text
            x={smallEndpoint.px + 12}
            y={smallEndpoint.py + 5}
            fill={SMALL_CODEBASE_COLOR}
            fontFamily={FONT_FAMILY}
            fontSize={18}
            fontWeight={600}
            opacity={forkLabelOpacity}
          >
            Small codebase
          </text>
          <text
            x={largeEndpoint.px + 12}
            y={largeEndpoint.py + 5}
            fill={LARGE_CODEBASE_COLOR}
            fontFamily={FONT_FAMILY}
            fontSize={18}
            fontWeight={600}
            opacity={forkLabelOpacity}
          >
            Large codebase
          </text>
        </>
      )}
    </svg>
  );
};

export default ForkingLines;
