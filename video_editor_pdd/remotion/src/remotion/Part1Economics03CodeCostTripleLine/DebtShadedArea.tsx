import React, { useMemo } from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  CHART_W,
  CHART_H,
  MARGIN,
  AMBER_LINE,
  TOTAL_COST_DATA,
  PATCH_COST_DATA,
  DEBT_FILL_START,
  DEBT_FILL_DUR,
  PULSE_START,
  PULSE_CYCLE,
  buildAreaD,
} from "./constants";

export const DebtShadedArea: React.FC = () => {
  const frame = useCurrentFrame();

  const areaD = useMemo(
    () => buildAreaD(TOTAL_COST_DATA, PATCH_COST_DATA),
    []
  );

  // Fill-in opacity: ramps from 0 to base opacity
  const fillProgress = interpolate(
    frame,
    [DEBT_FILL_START, DEBT_FILL_START + DEBT_FILL_DUR],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Pulse animation after fill completes (frame 540+)
  const pulsePhase =
    frame >= PULSE_START
      ? ((frame - PULSE_START) % PULSE_CYCLE) / PULSE_CYCLE
      : 0;

  // Sine pulse: 0.08 → 0.12 → 0.08
  const pulseOpacity =
    frame >= PULSE_START
      ? 0.08 + 0.04 * Math.sin(pulsePhase * Math.PI * 2)
      : 0.08;

  const baseOpacity = fillProgress * pulseOpacity;

  // "Debt label" positioned in the center of the shaded area
  const labelOpacity = interpolate(
    frame,
    [DEBT_FILL_START + DEBT_FILL_DUR - 30, DEBT_FILL_START + DEBT_FILL_DUR],
    [0, 0.5],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: MARGIN.left,
        top: MARGIN.top,
        width: CHART_W,
        height: CHART_H,
        pointerEvents: "none",
      }}
    >
      <svg
        width={CHART_W}
        height={CHART_H}
        viewBox={`0 0 ${CHART_W} ${CHART_H}`}
        style={{ overflow: "visible" }}
      >
        <path d={areaD} fill={AMBER_LINE} fillOpacity={baseOpacity} />

        {/* "Technical Debt" label centered in the shaded area */}
        <text
          x={CHART_W * 0.65}
          y={CHART_H * 0.42}
          textAnchor="middle"
          fill={AMBER_LINE}
          fillOpacity={labelOpacity}
          fontFamily="Inter, sans-serif"
          fontSize={14}
          fontStyle="italic"
        >
          Technical Debt
        </text>
      </svg>
    </div>
  );
};
