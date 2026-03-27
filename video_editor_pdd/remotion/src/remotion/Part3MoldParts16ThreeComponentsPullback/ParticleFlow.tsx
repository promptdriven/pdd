// ParticleFlow.tsx — continuous particle/stream animation through the mold
import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MOLD_CENTER_X,
  MOLD_TOP,
  MOLD_LEFT,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  NOZZLE_TOP,
  NOZZLE_HEIGHT,
  EXIT_TOP,
  EXIT_HEIGHT,
  COLOR_PROMPT,
  COLOR_GROUNDING,
  COLOR_WALLS,
  COLOR_OUTPUT,
  PARTICLE_COUNT,
  PARTICLE_CYCLE_FRAMES,
} from "./constants";

// Flow path waypoints (top to bottom)
const FLOW_PATH_POINTS = [
  { y: NOZZLE_TOP, region: "entry" },
  { y: NOZZLE_TOP + NOZZLE_HEIGHT, region: "nozzle" },
  { y: MOLD_TOP + 40, region: "cavity_start" },
  { y: MOLD_TOP + MOLD_HEIGHT / 2, region: "cavity_mid" },
  { y: MOLD_TOP + MOLD_HEIGHT - 80, region: "walls" },
  { y: MOLD_TOP + MOLD_HEIGHT - 10, region: "exit_start" },
  { y: EXIT_TOP + EXIT_HEIGHT + 30, region: "exit" },
] as const;

const PATH_TOP = FLOW_PATH_POINTS[0].y;
const PATH_BOTTOM = FLOW_PATH_POINTS[FLOW_PATH_POINTS.length - 1].y;
const PATH_LENGTH = PATH_BOTTOM - PATH_TOP;

// Compute color for a particle based on its vertical position
function getParticleColor(y: number): string {
  const nozzleEnd = MOLD_TOP + 40;
  const cavityMid = MOLD_TOP + MOLD_HEIGHT / 2;
  const wallsY = MOLD_TOP + MOLD_HEIGHT - 80;
  const exitY = MOLD_TOP + MOLD_HEIGHT;

  if (y < nozzleEnd) return COLOR_PROMPT;
  if (y < cavityMid) {
    // Transition from amber to teal
    const t = (y - nozzleEnd) / (cavityMid - nozzleEnd);
    return lerpColor(COLOR_PROMPT, COLOR_GROUNDING, t);
  }
  if (y < wallsY) return COLOR_GROUNDING;
  if (y < exitY) {
    // Transition from teal/blue to cyan
    const t = (y - wallsY) / (exitY - wallsY);
    return lerpColor(COLOR_WALLS, COLOR_OUTPUT, t);
  }
  return COLOR_OUTPUT;
}

// Simple hex color lerp
function lerpColor(a: string, b: string, t: number): string {
  const clamp = Math.max(0, Math.min(1, t));
  const ra = parseInt(a.slice(1, 3), 16);
  const ga = parseInt(a.slice(3, 5), 16);
  const ba = parseInt(a.slice(5, 7), 16);
  const rb = parseInt(b.slice(1, 3), 16);
  const gb = parseInt(b.slice(3, 5), 16);
  const bb = parseInt(b.slice(5, 7), 16);
  const r = Math.round(ra + (rb - ra) * clamp);
  const g = Math.round(ga + (gb - ga) * clamp);
  const bv = Math.round(ba + (bb - ba) * clamp);
  return `#${r.toString(16).padStart(2, "0")}${g.toString(16).padStart(2, "0")}${bv.toString(16).padStart(2, "0")}`;
}

// Spark component for wall contact
const WallSpark: React.FC<{
  x: number;
  y: number;
  progress: number;
}> = ({ x, y, progress }) => {
  const sparkOpacity = interpolate(progress, [0, 0.3, 1], [0, 1, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const sparkScale = interpolate(progress, [0, 0.2, 1], [0.3, 1, 0.1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.exp),
  });

  return (
    <g opacity={sparkOpacity} transform={`translate(${x}, ${y}) scale(${sparkScale})`}>
      <line x1={-8} y1={0} x2={8} y2={0} stroke={COLOR_WALLS} strokeWidth={2} />
      <line x1={0} y1={-8} x2={0} y2={8} stroke={COLOR_WALLS} strokeWidth={2} />
      <line x1={-5} y1={-5} x2={5} y2={5} stroke={COLOR_WALLS} strokeWidth={1.5} />
      <line x1={5} y1={-5} x2={-5} y2={5} stroke={COLOR_WALLS} strokeWidth={1.5} />
    </g>
  );
};

export const ParticleFlow: React.FC = () => {
  const frame = useCurrentFrame();

  // Flow starts at frame 30
  const flowFrame = frame - 30;
  if (flowFrame < 0) return null;

  // Central flow stream (glowing line)
  const streamProgress = interpolate(flowFrame, [0, 90], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const streamEndY = PATH_TOP + PATH_LENGTH * streamProgress;

  // Generate particles
  const particles: React.ReactNode[] = [];
  for (let i = 0; i < PARTICLE_COUNT; i++) {
    const phase = i / PARTICLE_COUNT;
    // Each particle cycles through the path
    const cycleProgress =
      ((flowFrame / PARTICLE_CYCLE_FRAMES + phase) % 1);

    // Only show particle if the stream has reached that far
    const particleY = PATH_TOP + PATH_LENGTH * cycleProgress;
    if (particleY > streamEndY + 20) continue;

    // Slight horizontal wobble
    const wobble = Math.sin(flowFrame * 0.15 + i * 2.5) * 12;
    const particleX = MOLD_CENTER_X + wobble;

    const color = getParticleColor(particleY);
    const size = 3 + Math.sin(i * 1.7) * 1.5;
    const opacity = 0.5 + Math.sin(flowFrame * 0.1 + i) * 0.3;

    particles.push(
      <circle
        key={`p-${i}`}
        cx={particleX}
        cy={particleY}
        r={size}
        fill={color}
        opacity={Math.max(0.2, opacity)}
      />
    );
  }

  // Wall sparks — appear when flow reaches the wall region (frame 90+)
  const sparks: React.ReactNode[] = [];
  if (flowFrame >= 60) {
    const sparkCount = 6;
    for (let s = 0; s < sparkCount; s++) {
      const sparkCycle = ((flowFrame - 60 + s * 11) % 40) / 40;
      const wallY = MOLD_TOP + MOLD_HEIGHT - 80 + Math.sin(s * 3) * 30;
      const side = s % 2 === 0 ? MOLD_LEFT + 20 : MOLD_LEFT + MOLD_WIDTH - 20;

      sparks.push(
        <WallSpark
          key={`spark-${s}`}
          x={side}
          y={wallY}
          progress={sparkCycle}
        />
      );
    }
  }

  // Central flow stream gradient
  const streamGradientId = "flowStreamGrad";

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <defs>
        <linearGradient id={streamGradientId} x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stopColor={COLOR_PROMPT} />
          <stop offset="35%" stopColor={COLOR_GROUNDING} />
          <stop offset="70%" stopColor={COLOR_WALLS} />
          <stop offset="100%" stopColor={COLOR_OUTPUT} />
        </linearGradient>
        <filter id="particleGlow" x="-100%" y="-100%" width="300%" height="300%">
          <feGaussianBlur stdDeviation="4" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Central stream line */}
      <line
        x1={MOLD_CENTER_X}
        y1={PATH_TOP}
        x2={MOLD_CENTER_X}
        y2={streamEndY}
        stroke={`url(#${streamGradientId})`}
        strokeWidth={4}
        opacity={0.6}
        strokeLinecap="round"
      />

      {/* Glow behind stream */}
      <line
        x1={MOLD_CENTER_X}
        y1={PATH_TOP}
        x2={MOLD_CENTER_X}
        y2={streamEndY}
        stroke={`url(#${streamGradientId})`}
        strokeWidth={12}
        opacity={0.15}
        strokeLinecap="round"
      />

      {/* Particles */}
      <g filter="url(#particleGlow)">{particles}</g>

      {/* Wall sparks */}
      {sparks}
    </svg>
  );
};

export default ParticleFlow;
