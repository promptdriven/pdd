import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  GHOST_LINE_A_COLOR,
  GHOST_LINE_B_COLOR,
  GHOST_LINE_OPACITY,
  GHOST_LINE_STROKE,
  GHOST_GLOW_COLOR,
  GHOST_GLOW_OPACITY,
  GHOST_GLOW_RADIUS,
  GHOST_DRAW_DURATION,
  PULSE_CYCLE_FRAMES,
} from "./constants";

/**
 * Two crossing lines (one descending, one ascending) drawn via
 * stroke-dashoffset, with a subtle glow at their intersection and
 * a gentle opacity pulse during the hold phase.
 */
export const CrossingLines: React.FC<{ drawProgress: number }> = ({
  drawProgress,
}) => {
  const frame = useCurrentFrame();

  // Subtle pulse in opacity (±0.01 around base 0.04)
  const pulse = interpolate(
    frame % PULSE_CYCLE_FRAMES,
    [0, PULSE_CYCLE_FRAMES / 2, PULSE_CYCLE_FRAMES],
    [0, 0.01, 0],
    { easing: Easing.inOut(Easing.sin) }
  );
  const lineOpacity = GHOST_LINE_OPACITY + pulse;

  // Line geometry — spanning most of the canvas
  const margin = 300;
  // Descending line: top-left to bottom-right
  const lineA = {
    x1: margin,
    y1: 250,
    x2: WIDTH - margin,
    y2: HEIGHT - 250,
  };
  // Ascending line: bottom-left to top-right
  const lineB = {
    x1: margin,
    y1: HEIGHT - 250,
    x2: WIDTH - margin,
    y2: 250,
  };

  // Intersection point (midpoint since lines are symmetric about center)
  const cx = WIDTH / 2;
  const cy = HEIGHT / 2;

  // Path length approximation
  const pathLength = Math.sqrt(
    (lineA.x2 - lineA.x1) ** 2 + (lineA.y2 - lineA.y1) ** 2
  );

  const dashOffset = pathLength * (1 - drawProgress);

  return (
    <AbsoluteFill>
      <svg width={WIDTH} height={HEIGHT}>
        {/* Radial glow at intersection */}
        <defs>
          <radialGradient id="ghost-glow" cx="50%" cy="50%" r="50%">
            <stop
              offset="0%"
              stopColor={GHOST_GLOW_COLOR}
              stopOpacity={GHOST_GLOW_OPACITY * drawProgress}
            />
            <stop offset="100%" stopColor={GHOST_GLOW_COLOR} stopOpacity={0} />
          </radialGradient>
        </defs>

        {/* Descending line */}
        <line
          x1={lineA.x1}
          y1={lineA.y1}
          x2={lineA.x2}
          y2={lineA.y2}
          stroke={GHOST_LINE_A_COLOR}
          strokeWidth={GHOST_LINE_STROKE}
          opacity={lineOpacity}
          strokeDasharray={pathLength}
          strokeDashoffset={dashOffset}
        />

        {/* Ascending line */}
        <line
          x1={lineB.x1}
          y1={lineB.y1}
          x2={lineB.x2}
          y2={lineB.y2}
          stroke={GHOST_LINE_B_COLOR}
          strokeWidth={GHOST_LINE_STROKE}
          opacity={lineOpacity}
          strokeDasharray={pathLength}
          strokeDashoffset={dashOffset}
        />

        {/* Glow at crossing point */}
        <circle
          cx={cx}
          cy={cy}
          r={GHOST_GLOW_RADIUS}
          fill="url(#ghost-glow)"
        />
      </svg>
    </AbsoluteFill>
  );
};

export default CrossingLines;
