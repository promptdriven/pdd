import React from "react";
import { Easing, interpolate, spring, useCurrentFrame, useVideoConfig } from "remotion";
import {
  BEATS,
  COLORS,
  CHART_MARGINS,
  YEAR_RANGE,
  HOURS_RANGE,
  CHART_DATA,
  YEAR_COUNTER,
} from "./constants";

export const GapIndicator: React.FC = () => {
  const frame = useCurrentFrame();
  const { width, height, fps } = useVideoConfig();

  const chartWidth = width - CHART_MARGINS.left - CHART_MARGINS.right;
  const chartHeight = height - CHART_MARGINS.top - CHART_MARGINS.bottom;

  const getXPosition = (year: number) => {
    return (
      CHART_MARGINS.left +
      ((year - YEAR_RANGE.min) / (YEAR_RANGE.max - YEAR_RANGE.min)) * chartWidth
    );
  };

  const getYPosition = (hours: number) => {
    return (
      CHART_MARGINS.top +
      chartHeight -
      (hours / HOURS_RANGE.max) * chartHeight
    );
  };

  // Gap indicator appears after shaded region
  const indicatorOpacity = interpolate(
    frame,
    [BEATS.GAP_INDICATOR_START, BEATS.GAP_INDICATOR_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  if (indicatorOpacity <= 0) {
    return null;
  }

  // Calculate current animated year
  const currentYear = interpolate(
    frame,
    [BEATS.TIME_PROGRESS_START, BEATS.TIME_PROGRESS_END],
    [YEAR_COUNTER.startYear, YEAR_COUNTER.endYear],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Get the cost to buy value at current year
  const getCostToBuyAtYear = (year: number): number => {
    const data = CHART_DATA.costToBuyFull;
    for (let i = 0; i < data.length - 1; i++) {
      if (year >= data[i].year && year <= data[i + 1].year) {
        const t = (year - data[i].year) / (data[i + 1].year - data[i].year);
        return data[i].hours + t * (data[i + 1].hours - data[i].hours);
      }
    }
    return data[data.length - 1].hours;
  };

  // Position the gap indicator at a fixed year (e.g., 2000) or current year
  const indicatorYear = Math.min(2000, currentYear);
  const indicatorX = getXPosition(indicatorYear);

  // Repair line is at 0.5 hours
  const repairY = getYPosition(0.5);
  const buyValue = getCostToBuyAtYear(indicatorYear);
  const buyY = getYPosition(buyValue);

  // Spring animation for arrow appearance
  const springProgress = spring({
    frame: frame - BEATS.GAP_INDICATOR_START,
    fps,
    config: {
      damping: 15,
      stiffness: 80,
    },
  });

  // Arrow dimensions
  const arrowHeadSize = 12;

  // Calculate the gap value for display
  const gapValue = (0.5 - buyValue).toFixed(2);

  // Pulsing effect on hold
  const holdPulse = frame >= BEATS.HOLD_START
    ? 1 + 0.03 * Math.sin((frame - BEATS.HOLD_START) * 0.1)
    : 1;

  return (
    <>
      <svg
        width={width}
        height={height}
        style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
      >
        <defs>
          {/* Arrow marker for the gap line - pointing down to irrational zone */}
          <marker
            id="arrowDown"
            markerWidth={arrowHeadSize}
            markerHeight={arrowHeadSize}
            refX={arrowHeadSize / 2}
            refY={0}
            orient="auto"
          >
            <polygon
              points={`0,0 ${arrowHeadSize / 2},${arrowHeadSize} ${arrowHeadSize},0`}
              fill={COLORS.GAP_INDICATOR}
            />
          </marker>

          {/* Glow filter */}
          <filter id="gapGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur in="SourceGraphic" stdDeviation="4" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Vertical line showing the gap with arrow pointing to irrational zone */}
        <line
          x1={indicatorX}
          y1={repairY}
          x2={indicatorX}
          y2={buyY - arrowHeadSize}
          stroke={COLORS.GAP_INDICATOR}
          strokeWidth={3}
          opacity={indicatorOpacity * springProgress}
          strokeDasharray="6,4"
          markerEnd="url(#arrowDown)"
          filter="url(#gapGlow)"
          style={{
            transform: `scale(${holdPulse})`,
            transformOrigin: `${indicatorX}px ${(repairY + buyY) / 2}px`,
          }}
        />

        {/* Horizontal reference lines */}
        <line
          x1={indicatorX - 15}
          y1={repairY}
          x2={indicatorX + 15}
          y2={repairY}
          stroke={COLORS.GAP_INDICATOR}
          strokeWidth={2}
          opacity={indicatorOpacity * springProgress * 0.8}
        />
        <line
          x1={indicatorX - 15}
          y1={buyY}
          x2={indicatorX + 15}
          y2={buyY}
          stroke={COLORS.GAP_INDICATOR}
          strokeWidth={2}
          opacity={indicatorOpacity * springProgress * 0.8}
        />
      </svg>

      {/* Gap value label - positioned above the arrow with emotional messaging */}
      <div
        style={{
          position: "absolute",
          left: indicatorX + 25,
          top: repairY - 50,
          transform: `translateY(-50%) scale(${holdPulse})`,
          opacity: indicatorOpacity * springProgress,
          fontFamily: "Inter, system-ui, sans-serif",
          fontSize: 20,
          fontWeight: 600,
          fontStyle: "italic",
          color: COLORS.GAP_INDICATOR,
          textShadow: `0 0 15px ${COLORS.GAP_INDICATOR}, 0 2px 8px rgba(0,0,0,0.8)`,
          whiteSpace: "nowrap",
          padding: "6px 12px",
          backgroundColor: "rgba(26, 26, 46, 0.9)",
          borderRadius: 6,
          border: `2px solid ${COLORS.GAP_INDICATOR}`,
        }}
      >
        Waste of time
      </div>
    </>
  );
};
