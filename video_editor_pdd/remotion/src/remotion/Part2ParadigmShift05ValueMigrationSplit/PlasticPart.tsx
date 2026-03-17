import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  PLASTIC_CENTER_X,
  PLASTIC_CENTER_Y,
  PLASTIC_COLOR,
  PLASTIC_OPACITY,
  PLASTIC_LABEL_COLOR,
  PLASTIC_FLOW_START,
  PLASTIC_FLOW_END,
  DISSOLVE_START,
  DISSOLVE_DURATION,
  REGEN_START,
  REGEN_DURATION,
} from "./constants";

const PANEL_WIDTH = 958;
const PART_WIDTH = 200;
const PART_HEIGHT = 80;

// Generate deterministic particles for dissolve effect
const PARTICLES = Array.from({ length: 24 }, (_, i) => ({
  angle: (i * 15 + 7) % 360,
  distance: 30 + (i * 13) % 60,
  size: 3 + (i % 4),
  delay: (i * 0.7) % 10,
}));

export const PlasticPart: React.FC = () => {
  const frame = useCurrentFrame();

  // Initial flow-in
  const flowIn = interpolate(
    frame,
    [PLASTIC_FLOW_START, PLASTIC_FLOW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Dissolve phase
  const dissolveProgress = interpolate(
    frame,
    [DISSOLVE_START, DISSOLVE_START + DISSOLVE_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
  );

  // Regeneration phase
  const regenProgress = interpolate(
    frame,
    [REGEN_START, REGEN_START + REGEN_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Determine which phase we're in
  const isPreDissolve = frame < DISSOLVE_START;
  const isDissolving = frame >= DISSOLVE_START && frame < REGEN_START;
  const isRegenerating = frame >= REGEN_START;

  let mainOpacity: number;
  if (isPreDissolve) {
    mainOpacity = flowIn * PLASTIC_OPACITY;
  } else if (isDissolving) {
    mainOpacity = (1 - dissolveProgress) * PLASTIC_OPACITY;
  } else {
    mainOpacity = regenProgress * PLASTIC_OPACITY;
  }

  const partX = PLASTIC_CENTER_X - PART_WIDTH / 2;
  const partY = PLASTIC_CENTER_Y - PART_HEIGHT / 2;

  return (
    <svg
      width={PANEL_WIDTH}
      height={1080}
      viewBox={`0 0 ${PANEL_WIDTH} 1080`}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Main plastic part shape */}
      <rect
        x={partX}
        y={partY}
        width={PART_WIDTH}
        height={PART_HEIGHT}
        rx={6}
        fill={PLASTIC_COLOR}
        opacity={mainOpacity}
      />
      {/* Part surface detail */}
      {mainOpacity > 0.1 && (
        <g opacity={mainOpacity * 0.5}>
          <line
            x1={partX + 20}
            y1={partY + PART_HEIGHT / 2}
            x2={partX + PART_WIDTH - 20}
            y2={partY + PART_HEIGHT / 2}
            stroke={PLASTIC_COLOR}
            strokeWidth={1}
            opacity={0.3}
          />
        </g>
      )}

      {/* "disposable" label */}
      {frame >= PLASTIC_FLOW_END && (
        <text
          x={PLASTIC_CENTER_X}
          y={PLASTIC_CENTER_Y + PART_HEIGHT / 2 + 20}
          textAnchor="middle"
          fontFamily="Inter, sans-serif"
          fontSize={9}
          fill={PLASTIC_LABEL_COLOR}
          opacity={isDissolving ? mainOpacity : (isRegenerating ? regenProgress * 0.3 : 0.3)}
        >
          disposable
        </text>
      )}

      {/* Dissolve particles */}
      {isDissolving &&
        PARTICLES.map((p, i) => {
          const particleProgress = Math.min(
            1,
            Math.max(0, (dissolveProgress * 20 - p.delay) / (20 - p.delay))
          );
          const rad = (p.angle * Math.PI) / 180;
          const dx = Math.cos(rad) * p.distance * particleProgress;
          const dy = Math.sin(rad) * p.distance * particleProgress - particleProgress * 20;
          const particleOpacity = (1 - particleProgress) * PLASTIC_OPACITY;

          return (
            <circle
              key={`particle-${i}`}
              cx={PLASTIC_CENTER_X + dx}
              cy={PLASTIC_CENTER_Y + dy}
              r={p.size * (1 - particleProgress * 0.5)}
              fill={PLASTIC_COLOR}
              opacity={particleOpacity}
            />
          );
        })}
    </svg>
  );
};
