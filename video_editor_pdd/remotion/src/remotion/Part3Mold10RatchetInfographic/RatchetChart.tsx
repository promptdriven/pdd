import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BAR_DATA,
  BAR_WIDTH,
  TIMELINE_Y,
  BARS_START,
  BARS_END,
  TOTAL_BARS,
  TEST_GREEN,
  TEST_GREEN_70,
  RATCHET_LINE_WIDTH,
  PULSE_START,
  PULSE_PERIOD,
  FADEOUT_START,
} from "./constants";

export const RatchetChart: React.FC = () => {
  const frame = useCurrentFrame();

  // How many bars are currently visible (spread evenly across BARS_START→BARS_END)
  const barDuration = BARS_END - BARS_START;
  const barsPerFrame = TOTAL_BARS / barDuration;
  const visibleCount = Math.min(
    TOTAL_BARS,
    Math.max(0, Math.floor((frame - BARS_START) * barsPerFrame))
  );

  if (visibleCount <= 0) return null;

  // Subtle pulse on the line during hold phase (frame 180-300)
  const pulseOpacity =
    frame >= PULSE_START && frame < FADEOUT_START
      ? 0.85 +
        0.15 *
          Math.sin(((frame - PULSE_START) / PULSE_PERIOD) * Math.PI * 2)
      : 1;

  // Build the stepped ratchet line path + fill area
  const visibleBars = BAR_DATA.slice(0, visibleCount);
  let linePath = "";
  let fillPath = "";

  if (visibleBars.length > 0) {
    const firstBar = visibleBars[0];
    const firstY = TIMELINE_Y - firstBar.cumulativeMax;

    linePath = `M ${firstBar.x} ${firstY}`;
    fillPath = `M ${firstBar.x} ${TIMELINE_Y} L ${firstBar.x} ${firstY}`;

    for (let i = 1; i < visibleBars.length; i++) {
      const prev = visibleBars[i - 1];
      const curr = visibleBars[i];
      const prevY = TIMELINE_Y - prev.cumulativeMax;
      const currY = TIMELINE_Y - curr.cumulativeMax;

      // Stepped: horizontal to new x, then vertical to new y
      linePath += ` L ${curr.x} ${prevY}`;
      fillPath += ` L ${curr.x} ${prevY}`;
      if (currY !== prevY) {
        linePath += ` L ${curr.x} ${currY}`;
        fillPath += ` L ${curr.x} ${currY}`;
      }
    }

    // Close fill path back to timeline
    const lastBar = visibleBars[visibleBars.length - 1];
    fillPath += ` L ${lastBar.x} ${TIMELINE_Y} Z`;
  }

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          {/* Gradient fill below the ratchet line: green 10% at top → transparent at bottom */}
          <linearGradient
            id="ratchetFillGrad"
            x1="0"
            y1="0"
            x2="0"
            y2="1"
          >
            <stop offset="0%" stopColor={TEST_GREEN} stopOpacity={0.15} />
            <stop offset="100%" stopColor={TEST_GREEN} stopOpacity={0} />
          </linearGradient>
          {/* Glow filter for the ratchet line: 0 0 8px rgba(34, 197, 94, 0.5) */}
          <filter
            id="ratchetGlow"
            x="-20%"
            y="-20%"
            width="140%"
            height="140%"
          >
            <feGaussianBlur stdDeviation="4" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Gradient fill below ratchet line */}
        {fillPath && (
          <path d={fillPath} fill="url(#ratchetFillGrad)" opacity={0.6} />
        )}

        {/* Test bars — vertical rectangles rising from timeline */}
        {visibleBars.map((bar, i) => {
          // Each bar pops up with easeOutQuad
          const barAppearFrame =
            BARS_START + (i / TOTAL_BARS) * (BARS_END - BARS_START);
          const barProgress = interpolate(
            frame,
            [barAppearFrame, barAppearFrame + 4],
            [0, 1],
            {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
              easing: Easing.out(Easing.quad),
            }
          );

          const barHeight = bar.height * barProgress;

          return (
            <rect
              key={`bar-${bar.index}`}
              x={bar.x - BAR_WIDTH / 2}
              y={TIMELINE_Y - barHeight}
              width={BAR_WIDTH}
              height={barHeight}
              fill={TEST_GREEN_70}
              rx={2}
            />
          );
        })}

        {/* Ratchet stepped line — monotonically increasing */}
        {linePath && (
          <path
            d={linePath}
            fill="none"
            stroke={TEST_GREEN}
            strokeWidth={RATCHET_LINE_WIDTH}
            strokeLinecap="round"
            strokeLinejoin="round"
            opacity={pulseOpacity}
            filter="url(#ratchetGlow)"
          />
        )}
      </svg>
    </AbsoluteFill>
  );
};

export default RatchetChart;
