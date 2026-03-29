import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  GHOST_UP_CURVE_COLOR,
  GHOST_FLAT_LINE_COLOR,
  GHOST_CURVE_OPACITY,
  GHOST_STROKE_WIDTH,
  GHOST_GLOW_COLOR,
  GHOST_GLOW_OPACITY,
  GHOST_GLOW_RADIUS,
  CURVES_DRAW_DURATION,
  PULSE_CYCLE_FRAMES,
} from "./constants";

/**
 * Two ghost curves: one exponential going up, one flat.
 * They diverge from a common origin at bottom-left-ish.
 */
export const DivergingCurves: React.FC<{ globalFrame: number }> = ({
  globalFrame,
}) => {
  const frame = useCurrentFrame();

  // Draw progress (0 → 1) over CURVES_DRAW_DURATION frames
  const drawProgress = interpolate(frame, [0, CURVES_DRAW_DURATION], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.bezier(0.42, 0, 0.58, 1), // easeInOut(cubic)
  });

  // Subtle pulse on the opacity once fully drawn
  const pulsePhase = ((globalFrame % PULSE_CYCLE_FRAMES) / PULSE_CYCLE_FRAMES) * Math.PI * 2;
  const pulse = Math.sin(pulsePhase);
  const opacityMultiplier = drawProgress >= 1 ? 1 + pulse * 0.3 : 1;

  const upCurveOpacity = GHOST_CURVE_OPACITY * opacityMultiplier;
  const flatLineOpacity = GHOST_CURVE_OPACITY * opacityMultiplier;

  // Build exponential curve path (bottom-left → top-right)
  const startX = 200;
  const endX = CANVAS_WIDTH - 200;
  const startY = CANVAS_HEIGHT - 200;
  const flatY = startY;
  const steps = 80;

  let upPath = "";
  let flatPath = "";

  for (let i = 0; i <= steps; i++) {
    const t = i / steps;
    const x = startX + (endX - startX) * t;
    // Exponential rise: y goes from startY up
    const expFactor = Math.pow(t, 2.5);
    const upY = startY - expFactor * 600;
    const cmd = i === 0 ? "M" : "L";
    upPath += `${cmd} ${x} ${upY} `;
    flatPath += `${cmd} ${x} ${flatY} `;
  }

  // Divergence point (where curves start separating noticeably) — roughly at 60% x
  const divX = startX + (endX - startX) * 0.6;
  const divExpFactor = Math.pow(0.6, 2.5);
  const divY = startY - divExpFactor * 600;
  const glowCenterY = (divY + flatY) / 2;

  // stroke-dasharray / dashoffset for draw animation
  const totalLength = 2000; // generous estimate
  const dashOffset = totalLength * (1 - drawProgress);

  return (
    <AbsoluteFill>
      <svg
        width={CANVAS_WIDTH}
        height={CANVAS_HEIGHT}
        viewBox={`0 0 ${CANVAS_WIDTH} ${CANVAS_HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Radial glow at divergence */}
        <defs>
          <radialGradient id="divGlow" cx="50%" cy="50%" r="50%">
            <stop offset="0%" stopColor={GHOST_GLOW_COLOR} stopOpacity={GHOST_GLOW_OPACITY * opacityMultiplier} />
            <stop offset="100%" stopColor={GHOST_GLOW_COLOR} stopOpacity={0} />
          </radialGradient>
        </defs>

        {drawProgress > 0.5 && (
          <circle
            cx={divX}
            cy={glowCenterY}
            r={GHOST_GLOW_RADIUS}
            fill="url(#divGlow)"
            opacity={interpolate(drawProgress, [0.5, 1], [0, 1], {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            })}
          />
        )}

        {/* Upward exponential curve */}
        <path
          d={upPath}
          fill="none"
          stroke={GHOST_UP_CURVE_COLOR}
          strokeWidth={GHOST_STROKE_WIDTH}
          opacity={upCurveOpacity}
          strokeDasharray={totalLength}
          strokeDashoffset={dashOffset}
          strokeLinecap="round"
        />

        {/* Flat horizontal line */}
        <path
          d={flatPath}
          fill="none"
          stroke={GHOST_FLAT_LINE_COLOR}
          strokeWidth={GHOST_STROKE_WIDTH}
          opacity={flatLineOpacity}
          strokeDasharray={totalLength}
          strokeDashoffset={dashOffset}
          strokeLinecap="round"
        />
      </svg>
    </AbsoluteFill>
  );
};
