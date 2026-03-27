import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  ARROW_COLOR,
  ARROW_LINE_WIDTH,
  FONT_FAMILY,
  SMALL_CODEBASE_DATA,
  LARGE_CODEBASE_DATA,
  PHASE_ARROW_START,
  ARROW_DRAW_DURATION,
  PHASE_ARROW_LABEL_START,
  FADE_DURATION,
} from "./constants";
import { xToPixel, yToPixel } from "./ChartAxes";

/**
 * Curved arrow from the small codebase line sweeping upward to the large
 * codebase line, with an animated draw-on effect and "Every patch adds code." label.
 */
const TrapArrow: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Arrow draw progress ───────────────────────────────
  const drawProgress = interpolate(
    frame,
    [PHASE_ARROW_START, PHASE_ARROW_START + ARROW_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // ── Arrow label fade ──────────────────────────────────
  const labelOpacity = interpolate(
    frame,
    [PHASE_ARROW_LABEL_START, PHASE_ARROW_LABEL_START + FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  if (frame < PHASE_ARROW_START) return null;

  // ── Arrow endpoints ───────────────────────────────────
  // From: end of small codebase line (2025, ~0.14 interpolated)
  const fromX = xToPixel(2025);
  const fromY = yToPixel(0.14);

  // To: midpoint of large codebase line (2024, 0.46)
  const toX = xToPixel(2024);
  const toY = yToPixel(0.46);

  // Control points for the cubic Bezier curve (sweeping upward)
  const cp1x = fromX + 40;
  const cp1y = fromY - 180;
  const cp2x = toX + 60;
  const cp2y = toY + 80;

  const pathD = `M ${fromX} ${fromY} C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${toX} ${toY}`;

  // We need a total path length for dash-offset animation.
  // Approximate; will be set dynamically via pathLength.
  const totalLength = 600;

  // Arrowhead at the end
  const arrowSize = 10;
  // Approximate tangent at the end of the curve
  const tangentX = toX - cp2x;
  const tangentY = toY - cp2y;
  const angle = Math.atan2(tangentY, tangentX);
  const arrowP1x = toX - arrowSize * Math.cos(angle - 0.4);
  const arrowP1y = toY - arrowSize * Math.sin(angle - 0.4);
  const arrowP2x = toX - arrowSize * Math.cos(angle + 0.4);
  const arrowP2y = toY - arrowSize * Math.sin(angle + 0.4);

  // Label position — midpoint of the curve
  const labelX = (fromX + toX) / 2 + 50;
  const labelY = (fromY + toY) / 2 - 60;

  return (
    <div style={{ position: "absolute", inset: 0, pointerEvents: "none" }}>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* ── Curved dashed arrow ──────────────────── */}
        <path
          d={pathD}
          fill="none"
          stroke={ARROW_COLOR}
          strokeWidth={ARROW_LINE_WIDTH}
          strokeDasharray="6 4"
          pathLength={totalLength}
          strokeDashoffset={totalLength * (1 - drawProgress)}
          strokeLinecap="round"
        />

        {/* ── Arrowhead ───────────────────────────── */}
        {drawProgress > 0.85 && (
          <polygon
            points={`${toX},${toY} ${arrowP1x},${arrowP1y} ${arrowP2x},${arrowP2y}`}
            fill={ARROW_COLOR}
            opacity={interpolate(
              drawProgress,
              [0.85, 1],
              [0, 1],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            )}
          />
        )}

        {/* ── Start dot ──────────────────────────── */}
        <circle
          cx={fromX}
          cy={fromY}
          r={4}
          fill={ARROW_COLOR}
          opacity={drawProgress > 0 ? 1 : 0}
        />
      </svg>

      {/* ── Arrow label ──────────────────────────── */}
      {frame >= PHASE_ARROW_LABEL_START && (
        <div
          style={{
            position: "absolute",
            left: labelX,
            top: labelY,
            opacity: labelOpacity,
            fontFamily: FONT_FAMILY,
            fontSize: 19,
            fontWeight: 700,
            color: ARROW_COLOR,
            textShadow: "0 2px 6px rgba(0,0,0,0.7)",
            whiteSpace: "nowrap",
          }}
        >
          Every patch adds code.
        </div>
      )}
    </div>
  );
};

export default TrapArrow;
