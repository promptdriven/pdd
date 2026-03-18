import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import { BLUE_GENERATE, PHASE_WE_ARE_HERE, PHASE_PROMPT_NOTE } from "./constants";

interface CrossingPointProps {
  cx: number;
  cy: number;
}

/**
 * Glowing dot + "We are here." label at the generation/patch crossing.
 * Also the small prompt annotation below.
 */
export const CrossingPoint: React.FC<CrossingPointProps> = ({ cx, cy }) => {
  const frame = useCurrentFrame();

  const showStart = PHASE_WE_ARE_HERE.start;

  // Main appear
  const appear = interpolate(
    frame,
    [showStart, showStart + 20],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Pulse glow
  const pulsePhase = Math.max(0, frame - showStart - 20);
  const glowScale = 1 + 0.3 * Math.sin((pulsePhase / 50) * Math.PI * 2);
  const glowOpacity = interpolate(
    Math.sin((pulsePhase / 50) * Math.PI * 2),
    [-1, 1],
    [0.1, 0.25],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Prompt annotation
  const promptOpacity = interpolate(
    frame,
    [PHASE_PROMPT_NOTE.start, PHASE_PROMPT_NOTE.start + 15],
    [0, 0.4],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  if (frame < showStart) return null;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Outer glow */}
      <circle
        cx={cx}
        cy={cy}
        r={20 * glowScale}
        fill={BLUE_GENERATE}
        opacity={glowOpacity * appear}
      />

      {/* Core dot */}
      <circle
        cx={cx}
        cy={cy}
        r={5}
        fill={BLUE_GENERATE}
        opacity={0.9 * appear}
      />

      {/* "We are here." label */}
      <text
        x={cx + 18}
        y={cy - 12}
        fill={BLUE_GENERATE}
        fontSize={16}
        fontFamily="Inter, sans-serif"
        fontWeight={700}
        opacity={0.85 * appear}
        filter="url(#labelGlow)"
      >
        We are here.
      </text>

      {/* Subtle glow filter */}
      <defs>
        <filter id="labelGlow" x="-20%" y="-20%" width="140%" height="140%">
          <feGaussianBlur stdDeviation="2" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Small prompt annotation */}
      <text
        x={cx + 18}
        y={cy + 10}
        fill={BLUE_GENERATE}
        fontSize={9}
        fontFamily="Inter, sans-serif"
        opacity={promptOpacity}
      >
        Small modules. Clear prompts. Always fits in context.
      </text>
    </svg>
  );
};

export default CrossingPoint;
