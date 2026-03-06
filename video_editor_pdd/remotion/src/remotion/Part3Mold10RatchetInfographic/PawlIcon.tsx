import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate } from "remotion";
import {
  BAR_DATA,
  TIMELINE_Y,
  BARS_START,
  BARS_END,
  TOTAL_BARS,
  WHITE,
} from "./constants";

/**
 * A ratchet pawl icon that slides along the top of the ratchet line.
 * Drawn as a small lock/pawl shape in white.
 */
export const PawlIcon: React.FC = () => {
  const frame = useCurrentFrame();

  // Determine current position along the ratchet line
  const barDuration = BARS_END - BARS_START;
  const barsPerFrame = TOTAL_BARS / barDuration;
  const visibleCount = Math.min(
    TOTAL_BARS,
    Math.max(0, Math.floor((frame - BARS_START) * barsPerFrame))
  );

  if (visibleCount <= 0) return null;

  const currentBar = BAR_DATA[Math.min(visibleCount - 1, TOTAL_BARS - 1)];
  const pawlX = currentBar.x;
  const pawlY = TIMELINE_Y - currentBar.cumulativeMax;

  // Fade in during first few bars
  const opacity = interpolate(frame, [BARS_START, BARS_START + 10], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Pawl icon: a small ratchet/lock shape */}
        <g
          transform={`translate(${pawlX}, ${pawlY - 28})`}
          opacity={opacity}
        >
          {/* Lock body */}
          <rect
            x={-8}
            y={8}
            width={16}
            height={14}
            rx={2}
            fill={WHITE}
          />
          {/* Lock shackle (the arch) */}
          <path
            d="M -5 8 L -5 3 A 5 5 0 0 1 5 3 L 5 8"
            fill="none"
            stroke={WHITE}
            strokeWidth={2.5}
            strokeLinecap="round"
          />
          {/* Keyhole dot */}
          <circle cx={0} cy={14} r={2} fill="#0A1628" />
          {/* Small arrow pointing down to the line */}
          <polygon
            points="-4,22 4,22 0,28"
            fill={WHITE}
          />
        </g>
      </svg>
    </AbsoluteFill>
  );
};

export default PawlIcon;
