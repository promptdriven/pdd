import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  INSET_X,
  INSET_Y,
  INSET_W,
  INSET_H,
  RED_HIGHLIGHT,
  FONT_FAMILY,
  PERFORMANCE_DATA,
  INSET_APPEAR_START,
  INSET_APPEAR_END,
  INSET_LINE_DRAW_START,
  INSET_LINE_DRAW_END,
  INSET_LABEL_START,
  INSET_LABEL_END,
} from "./constants";

// Chart margins within the inset
const MARGIN_TOP = 36;
const MARGIN_BOTTOM = 20;
const MARGIN_LEFT = 10;
const MARGIN_RIGHT = 10;
const CHART_W = INSET_W - MARGIN_LEFT - MARGIN_RIGHT;
const CHART_H = INSET_H - MARGIN_TOP - MARGIN_BOTTOM;

function dataToX(xVal: number): number {
  return MARGIN_LEFT + xVal * CHART_W;
}

function dataToY(yVal: number): number {
  return MARGIN_TOP + CHART_H * (1 - yVal / 100);
}

/**
 * InsetGraph — mini "Performance vs. Context Length" chart
 * in the lower-right corner with a declining red line,
 * EMNLP 2025 citation, and degradation range label.
 */
export const InsetGraph: React.FC = () => {
  const frame = useCurrentFrame();

  // Container fade in
  const containerOpacity = interpolate(
    frame,
    [INSET_APPEAR_START, INSET_APPEAR_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  if (containerOpacity <= 0) return null;

  // Line draw progress
  const drawProgress = interpolate(
    frame,
    [INSET_LINE_DRAW_START, INSET_LINE_DRAW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Label fade in
  const labelOpacity = interpolate(
    frame,
    [INSET_LABEL_START, INSET_LABEL_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Build SVG path for the declining line
  const visiblePoints = PERFORMANCE_DATA.filter((p) => p.x <= drawProgress);
  // Add interpolated endpoint
  if (drawProgress > 0 && drawProgress < 1) {
    const lastIdx = PERFORMANCE_DATA.findIndex((p) => p.x > drawProgress);
    if (lastIdx > 0) {
      const prev = PERFORMANCE_DATA[lastIdx - 1];
      const next = PERFORMANCE_DATA[lastIdx];
      const t = (drawProgress - prev.x) / (next.x - prev.x);
      visiblePoints.push({
        x: drawProgress,
        y: prev.y + (next.y - prev.y) * t,
      });
    }
  }

  let pathD = "";
  visiblePoints.forEach((p, i) => {
    const px = dataToX(p.x);
    const py = dataToY(p.y);
    pathD += i === 0 ? `M ${px} ${py}` : ` L ${px} ${py}`;
  });

  return (
    <div
      style={{
        position: "absolute",
        left: INSET_X,
        top: INSET_Y,
        width: INSET_W,
        height: INSET_H,
        opacity: containerOpacity,
        border: "1px solid rgba(51, 65, 85, 0.15)",
        borderRadius: 6,
        backgroundColor: "rgba(13, 17, 23, 0.9)",
        overflow: "hidden",
      }}
    >
      {/* Title */}
      <div
        style={{
          position: "absolute",
          top: 8,
          left: 12,
          fontFamily: FONT_FAMILY,
          fontSize: 10,
          fontWeight: 700,
          color: "#E2E8F0",
          opacity: 0.5,
        }}
      >
        Performance vs. Context Length
      </div>

      {/* SVG chart */}
      <svg
        width={INSET_W}
        height={INSET_H}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* X-axis baseline */}
        <line
          x1={MARGIN_LEFT}
          y1={MARGIN_TOP + CHART_H}
          x2={MARGIN_LEFT + CHART_W}
          y2={MARGIN_TOP + CHART_H}
          stroke="#334155"
          strokeWidth={1}
          opacity={0.3}
        />
        {/* Y-axis baseline */}
        <line
          x1={MARGIN_LEFT}
          y1={MARGIN_TOP}
          x2={MARGIN_LEFT}
          y2={MARGIN_TOP + CHART_H}
          stroke="#334155"
          strokeWidth={1}
          opacity={0.3}
        />

        {/* Declining performance line */}
        {pathD && (
          <path
            d={pathD}
            fill="none"
            stroke={RED_HIGHLIGHT}
            strokeWidth={2}
            strokeLinecap="round"
            strokeLinejoin="round"
          />
        )}
      </svg>

      {/* Range label */}
      <div
        style={{
          position: "absolute",
          bottom: 28,
          right: 12,
          fontFamily: FONT_FAMILY,
          fontSize: 10,
          color: RED_HIGHLIGHT,
          opacity: labelOpacity * 0.6,
          fontWeight: 600,
        }}
      >
        −14% to −85%
      </div>

      {/* Citation */}
      <div
        style={{
          position: "absolute",
          bottom: 6,
          right: 12,
          fontFamily: FONT_FAMILY,
          fontSize: 8,
          color: "#94A3B8",
          opacity: labelOpacity * 0.3,
        }}
      >
        EMNLP, 2025
      </div>
    </div>
  );
};

export default InsetGraph;
