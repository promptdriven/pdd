import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TIMELINE_MONTHS,
  TIMELINE_BAR_WIDTH,
  TIMELINE_BAR_GAP,
  TIMELINE_HEIGHT,
  TIMELINE_WIDTH,
  BAR_STAGGER,
} from "./constants";

interface MiniTimelineProps {
  type: "rising_bars" | "flat_sawtooth";
  color: string;
  animateStart: number;
  animateEnd: number;
}

/**
 * Mini timeline chart.
 * - rising_bars: bars that grow taller left-to-right (debt accumulates)
 * - flat_sawtooth: flat line with periodic sawtooth resets (debt resets)
 */
export const MiniTimeline: React.FC<MiniTimelineProps> = ({
  type,
  color,
  animateStart,
  animateEnd,
}) => {
  const frame = useCurrentFrame();

  if (type === "rising_bars") {
    return (
      <div style={{ position: "relative", width: TIMELINE_WIDTH, height: TIMELINE_HEIGHT }}>
        {/* Baseline */}
        <div
          style={{
            position: "absolute",
            bottom: 0,
            left: 0,
            width: TIMELINE_WIDTH,
            height: 1,
            backgroundColor: "rgba(255, 255, 255, 0.15)",
          }}
        />
        {Array.from({ length: TIMELINE_MONTHS }).map((_, i) => {
          // Height grows: each bar is taller than the last
          const maxH = 20 + (i / (TIMELINE_MONTHS - 1)) * (TIMELINE_HEIGHT - 30);
          const barStart = animateStart + i * BAR_STAGGER;
          const barEnd = barStart + (animateEnd - animateStart);

          const progress = interpolate(
            frame,
            [barStart, barEnd],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
          );

          const barH = maxH * progress;

          return (
            <div
              key={i}
              style={{
                position: "absolute",
                left: i * (TIMELINE_BAR_WIDTH + TIMELINE_BAR_GAP),
                bottom: 1,
                width: TIMELINE_BAR_WIDTH,
                height: barH,
                backgroundColor: color,
                borderRadius: 3,
                opacity: 0.8,
              }}
            />
          );
        })}
      </div>
    );
  }

  // flat_sawtooth: a flat green line with periodic drops (resets)
  const totalWidth = TIMELINE_WIDTH;
  const totalAnimDuration = animateEnd - animateStart;

  const drawProgress = interpolate(
    frame,
    [animateStart, animateStart + totalAnimDuration],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Build a sawtooth path: 4 cycles of rise then reset
  const cycles = 4;
  const segWidth = totalWidth / cycles;
  const flatY = TIMELINE_HEIGHT * 0.3; // line sits near top (low debt)
  const resetDropY = TIMELINE_HEIGHT * 0.7; // drop to higher debt before reset

  let pathD = `M 0 ${flatY}`;
  for (let c = 0; c < cycles; c++) {
    const x0 = c * segWidth;
    const x1 = x0 + segWidth * 0.75; // gradual rise
    const x2 = x0 + segWidth * 0.78; // sharp drop
    const x3 = x0 + segWidth;        // back to flat

    pathD += ` L ${x1} ${resetDropY}`;
    pathD += ` L ${x2} ${flatY}`;
    pathD += ` L ${x3} ${flatY}`;
  }

  // Clip path to show progressive drawing
  const visibleWidth = totalWidth * drawProgress;

  return (
    <div style={{ position: "relative", width: TIMELINE_WIDTH, height: TIMELINE_HEIGHT }}>
      {/* Baseline */}
      <div
        style={{
          position: "absolute",
          bottom: 0,
          left: 0,
          width: TIMELINE_WIDTH,
          height: 1,
          backgroundColor: "rgba(255, 255, 255, 0.15)",
        }}
      />
      <svg
        width={TIMELINE_WIDTH}
        height={TIMELINE_HEIGHT}
        viewBox={`0 0 ${TIMELINE_WIDTH} ${TIMELINE_HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <clipPath id="sawtooth-clip">
            <rect x="0" y="0" width={visibleWidth} height={TIMELINE_HEIGHT} />
          </clipPath>
        </defs>
        <path
          d={pathD}
          stroke={color}
          strokeWidth="3"
          fill="none"
          clipPath="url(#sawtooth-clip)"
          strokeLinecap="round"
          strokeLinejoin="round"
        />
      </svg>
    </div>
  );
};

export default MiniTimeline;
