import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TIMELINE_CHART_WIDTH,
  TIMELINE_CHART_HEIGHT,
  TIMELINE_MONTHS,
  LEFT_TIMELINE_START,
  LEFT_TIMELINE_END,
  RIGHT_TIMELINE_START,
  RIGHT_TIMELINE_END,
  SLATE_400,
} from "./constants";

interface MiniTimelineProps {
  type: "rising_bars" | "flat_sawtooth";
  color: string;
}

const BAR_GAP = 6;
const BAR_WIDTH = (TIMELINE_CHART_WIDTH - BAR_GAP * (TIMELINE_MONTHS - 1)) / TIMELINE_MONTHS;

// Deterministic bar heights for rising debt pattern
const RISING_HEIGHTS = [0.15, 0.22, 0.3, 0.35, 0.42, 0.5, 0.55, 0.62, 0.7, 0.78, 0.88, 1.0];

export const MiniTimeline: React.FC<MiniTimelineProps> = ({ type, color }) => {
  const frame = useCurrentFrame();

  const isLeft = type === "rising_bars";
  const animStart = isLeft ? LEFT_TIMELINE_START : RIGHT_TIMELINE_START;
  const animEnd = isLeft ? LEFT_TIMELINE_END : RIGHT_TIMELINE_END;

  // X-axis labels
  const axisY = TIMELINE_CHART_HEIGHT + 18;

  if (type === "rising_bars") {
    return (
      <svg
        width={TIMELINE_CHART_WIDTH}
        height={TIMELINE_CHART_HEIGHT + 30}
        viewBox={`0 0 ${TIMELINE_CHART_WIDTH} ${TIMELINE_CHART_HEIGHT + 30}`}
      >
        {/* Month labels */}
        {Array.from({ length: TIMELINE_MONTHS }).map((_, i) => {
          const x = i * (BAR_WIDTH + BAR_GAP) + BAR_WIDTH / 2;
          return (
            <text
              key={`month-${i}`}
              x={x}
              y={axisY}
              fill={SLATE_400}
              fontSize={11}
              fontFamily="Inter, sans-serif"
              fontWeight={400}
              textAnchor="middle"
              opacity={0.6}
            >
              {i + 1}
            </text>
          );
        })}

        {/* Rising bars */}
        {RISING_HEIGHTS.map((heightFrac, i) => {
          const staggerFrame = animStart + i * 3;
          const progress = interpolate(frame, [staggerFrame, staggerFrame + 8], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.quad),
          });

          const barH = heightFrac * TIMELINE_CHART_HEIGHT * progress;
          const x = i * (BAR_WIDTH + BAR_GAP);

          return (
            <rect
              key={`bar-${i}`}
              x={x}
              y={TIMELINE_CHART_HEIGHT - barH}
              width={BAR_WIDTH}
              height={barH}
              fill={color}
              rx={3}
              opacity={0.8}
            />
          );
        })}
      </svg>
    );
  }

  // Flat sawtooth — line that stays low with periodic resets
  const lineProgress = interpolate(frame, [animStart, animEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Build sawtooth path: 4 cycles of gradual rise then sharp drop
  const cycles = 4;
  const cycleWidth = TIMELINE_CHART_WIDTH / cycles;
  const baselineY = TIMELINE_CHART_HEIGHT - 10;
  const peakRise = 40; // pixels above baseline at peak debt

  let pathD = `M 0 ${baselineY}`;
  for (let c = 0; c < cycles; c++) {
    const startX = c * cycleWidth;
    const peakX = startX + cycleWidth * 0.85;
    const resetX = startX + cycleWidth * 0.88;
    const endX = startX + cycleWidth;

    // Gradual rise
    pathD += ` L ${peakX} ${baselineY - peakRise * 0.3}`;
    // Sharp drop back to baseline
    pathD += ` L ${resetX} ${baselineY}`;
    // Flat to next cycle
    pathD += ` L ${endX} ${baselineY}`;
  }

  // Clip the path to the progress
  const visibleWidth = TIMELINE_CHART_WIDTH * lineProgress;

  return (
    <svg
      width={TIMELINE_CHART_WIDTH}
      height={TIMELINE_CHART_HEIGHT + 30}
      viewBox={`0 0 ${TIMELINE_CHART_WIDTH} ${TIMELINE_CHART_HEIGHT + 30}`}
    >
      {/* Month labels */}
      {Array.from({ length: TIMELINE_MONTHS }).map((_, i) => {
        const x = i * (BAR_WIDTH + BAR_GAP) + BAR_WIDTH / 2;
        return (
          <text
            key={`month-${i}`}
            x={x}
            y={axisY}
            fill={SLATE_400}
            fontSize={11}
            fontFamily="Inter, sans-serif"
            fontWeight={400}
            textAnchor="middle"
            opacity={0.6}
          >
            {i + 1}
          </text>
        );
      })}

      {/* Baseline reference */}
      <line
        x1={0}
        y1={baselineY}
        x2={TIMELINE_CHART_WIDTH}
        y2={baselineY}
        stroke={color}
        strokeWidth={1}
        opacity={0.15}
        strokeDasharray="4 4"
      />

      {/* Sawtooth line with clip */}
      <defs>
        <clipPath id="sawtooth-clip">
          <rect x={0} y={0} width={visibleWidth} height={TIMELINE_CHART_HEIGHT + 30} />
        </clipPath>
      </defs>

      {/* Fill area under the sawtooth */}
      <path
        d={pathD + ` L ${TIMELINE_CHART_WIDTH} ${baselineY + 2} L 0 ${baselineY + 2} Z`}
        fill={color}
        opacity={0.08}
        clipPath="url(#sawtooth-clip)"
      />

      {/* The line itself */}
      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth={3}
        strokeLinecap="round"
        strokeLinejoin="round"
        clipPath="url(#sawtooth-clip)"
      />

      {/* Reset markers — small circles at each drop point */}
      {Array.from({ length: cycles }).map((_, c) => {
        const resetX = (c * cycleWidth + cycleWidth * 0.88);
        const markerOpacity = resetX <= visibleWidth ? 0.7 : 0;
        return (
          <circle
            key={`reset-${c}`}
            cx={resetX}
            cy={baselineY}
            r={4}
            fill={color}
            opacity={markerOpacity}
          />
        );
      })}
    </svg>
  );
};

export default MiniTimeline;
