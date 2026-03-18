import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { AMBER, BLUE, GREEN, TEXT_PRIMARY, TIMING } from "./constants";

/**
 * Cross-section mold diagram showing all three PDD components:
 * - Amber walls (Tests)
 * - Blue nozzle (Prompt)
 * - Green cavity fill (Grounding)
 *
 * Animates: starts centered at full scale, then slides left and shrinks.
 */
export const MoldDiagram: React.FC = () => {
  const frame = useCurrentFrame();

  // Position & scale animation (frames 60-100)
  const centerX = interpolate(
    frame,
    [TIMING.moldSlideStart, TIMING.moldSlideEnd],
    [960, 350],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );
  const centerY = 500;
  const scale = interpolate(
    frame,
    [TIMING.moldSlideStart, TIMING.moldSlideEnd],
    [1, 0.5],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  // Glow pulse for all regions
  const glowPulse = interpolate(
    frame % 60,
    [0, 30, 60],
    [0.6, 1, 0.6],
    { extrapolateRight: "clamp" }
  );

  // Flow animation progress (loops during first 60 frames, then static)
  const flowProgress = frame < 60
    ? interpolate(frame % 30, [0, 30], [0, 1])
    : 1;

  // After mold slides, keep a subtler flow
  const postSlideFlow = frame >= TIMING.moldSlideEnd
    ? interpolate(frame % 60, [0, 60], [0, 1])
    : 0;

  const activeFlow = frame < TIMING.moldSlideEnd ? flowProgress : postSlideFlow;

  return (
    <div
      style={{
        position: "absolute",
        left: centerX,
        top: centerY,
        transform: `translate(-50%, -50%) scale(${scale})`,
        width: 500,
        height: 600,
        transformOrigin: "center center",
      }}
    >
      <svg width={500} height={600} viewBox="0 0 500 600">
        {/* Outer glow */}
        <defs>
          <filter id="moldGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="8" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
          <filter id="flowGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="4" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Mold walls (amber) — left and right boundaries */}
        <rect
          x={40}
          y={100}
          width={30}
          height={400}
          rx={4}
          fill={AMBER}
          opacity={glowPulse * 0.7}
          filter="url(#moldGlow)"
        />
        <rect
          x={430}
          y={100}
          width={30}
          height={400}
          rx={4}
          fill={AMBER}
          opacity={glowPulse * 0.7}
          filter="url(#moldGlow)"
        />
        {/* Wall labels */}
        <text
          x={55}
          y={90}
          textAnchor="middle"
          fill={AMBER}
          fontSize={14}
          fontFamily="Inter"
          fontWeight={600}
          opacity={0.8}
        >
          Tests
        </text>
        <text
          x={445}
          y={90}
          textAnchor="middle"
          fill={AMBER}
          fontSize={14}
          fontFamily="Inter"
          fontWeight={600}
          opacity={0.8}
        >
          Tests
        </text>

        {/* Nozzle (blue) — top funnel */}
        <path
          d={`M 200,20 L 300,20 L 280,100 L 220,100 Z`}
          fill={BLUE}
          opacity={glowPulse * 0.6}
          filter="url(#moldGlow)"
        />
        <text
          x={250}
          y={15}
          textAnchor="middle"
          fill={BLUE}
          fontSize={14}
          fontFamily="Inter"
          fontWeight={600}
          opacity={0.8}
        >
          Prompt
        </text>

        {/* Cavity / Grounding (green) — center fill area */}
        <rect
          x={80}
          y={100}
          width={340}
          height={400}
          rx={8}
          fill={GREEN}
          opacity={glowPulse * 0.15}
        />
        <rect
          x={80}
          y={100}
          width={340}
          height={400}
          rx={8}
          fill="none"
          stroke={GREEN}
          strokeWidth={2}
          opacity={glowPulse * 0.5}
          filter="url(#moldGlow)"
        />
        <text
          x={250}
          y={310}
          textAnchor="middle"
          fill={GREEN}
          fontSize={16}
          fontFamily="Inter"
          fontWeight={600}
          opacity={0.7}
        >
          Grounding
        </text>

        {/* Flow particles — animated dots moving through the mold */}
        {[0, 0.2, 0.4, 0.6, 0.8].map((offset, i) => {
          const t = (activeFlow + offset) % 1;
          // Path: nozzle top → through cavity → bottom
          const py = 20 + t * 560;
          const px = 250 + Math.sin(t * Math.PI * 2 + i) * 30;
          // Color transitions: blue at top → green in middle → white at bottom
          const color = t < 0.3 ? BLUE : t < 0.7 ? GREEN : TEXT_PRIMARY;
          const particleOpacity = t < 0.1 || t > 0.95 ? 0.2 : 0.6;
          return (
            <circle
              key={i}
              cx={px}
              cy={py}
              r={4}
              fill={color}
              opacity={particleOpacity}
              filter="url(#flowGlow)"
            />
          );
        })}

        {/* Output slot — code emerges at bottom */}
        <rect
          x={150}
          y={510}
          width={200}
          height={40}
          rx={4}
          fill={TEXT_PRIMARY}
          opacity={0.1}
        />
        <text
          x={250}
          y={535}
          textAnchor="middle"
          fill={TEXT_PRIMARY}
          fontSize={11}
          fontFamily="monospace"
          opacity={0.5}
        >
          {"{ code output }"}
        </text>

        {/* Bottom label */}
        <text
          x={250}
          y={580}
          textAnchor="middle"
          fill={TEXT_PRIMARY}
          fontSize={12}
          fontFamily="Inter"
          opacity={0.4}
        >
          The Mold
        </text>
      </svg>
    </div>
  );
};
