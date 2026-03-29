import React from 'react';
import { AbsoluteFill, interpolate } from 'remotion';

interface GhostMoldProps {
  drawProgress: number; // 0..1 for stroke-dashoffset animation
  frame: number; // absolute frame for pulse calculations
}

/**
 * A ghostly SVG cross-section of an injection mold with three regions:
 * walls, nozzle, and cavity — drawn at very low opacity to foreshadow
 * the "three parts" thesis.
 */
export const GhostMold: React.FC<GhostMoldProps> = ({
  drawProgress,
  frame,
}) => {
  const PULSE_CYCLE = 60;

  // Each region pulses in sequence: walls at 0, nozzle at 20, cavity at 40
  const wallsPulse = interpolate(
    frame % PULSE_CYCLE,
    [0, 15, 30],
    [0, 1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );
  const nozzlePulse = interpolate(
    frame % PULSE_CYCLE,
    [20, 35, 50],
    [0, 1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );
  const cavityPulse = interpolate(
    frame % PULSE_CYCLE,
    [40, 55, 59],
    [0, 1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Base opacities with subtle pulse overlay
  const wallsOpacity = 0.04 + wallsPulse * 0.02;
  const nozzleOpacity = 0.03 + nozzlePulse * 0.015;
  const cavityOpacity = 0.03 + cavityPulse * 0.015;

  // Stroke dashoffset for draw-on animation
  const totalPathLength = 1200;
  const dashOffset = totalPathLength * (1 - drawProgress);

  const strokeDashProps = {
    strokeDasharray: totalPathLength,
    strokeDashoffset: dashOffset,
  };

  return (
    <AbsoluteFill
      style={{
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'center',
      }}
    >
      <svg
        width={600}
        height={500}
        viewBox="0 0 600 500"
        style={{ position: 'absolute', top: 290, left: 660 }}
      >
        {/* Walls region — outer rectangular shell */}
        <rect
          x={50}
          y={50}
          width={500}
          height={400}
          rx={8}
          fill="none"
          stroke="#4A90D9"
          strokeWidth={1.5}
          opacity={wallsOpacity}
          {...strokeDashProps}
        />
        {/* Inner wall contour */}
        <rect
          x={80}
          y={80}
          width={440}
          height={340}
          rx={4}
          fill="none"
          stroke="#4A90D9"
          strokeWidth={1.5}
          opacity={wallsOpacity}
          {...strokeDashProps}
        />

        {/* Nozzle region — funnel shape at top center */}
        <path
          d="M260 50 L260 20 Q300 0 340 20 L340 50"
          fill="none"
          stroke="#D9944A"
          strokeWidth={1.5}
          opacity={nozzleOpacity}
          {...strokeDashProps}
        />
        {/* Nozzle channel into mold */}
        <path
          d="M285 50 L285 120 Q300 140 315 120 L315 50"
          fill="none"
          stroke="#D9944A"
          strokeWidth={1.5}
          opacity={nozzleOpacity}
          {...strokeDashProps}
        />

        {/* Cavity region — the interior shape being molded */}
        <path
          d="M150 180 Q150 140 220 140 L380 140 Q450 140 450 180
             L450 350 Q450 390 380 390 L220 390 Q150 390 150 350 Z"
          fill="none"
          stroke="#4AD9A0"
          strokeWidth={1.5}
          opacity={cavityOpacity}
          {...strokeDashProps}
        />
        {/* Interior cavity detail */}
        <path
          d="M200 200 L400 200 L400 340 L200 340 Z"
          fill="none"
          stroke="#4AD9A0"
          strokeWidth={1}
          opacity={cavityOpacity * 0.7}
          {...strokeDashProps}
        />

        {/* Parting line indicators */}
        <line
          x1={50}
          y1={250}
          x2={80}
          y2={250}
          stroke="#4A90D9"
          strokeWidth={1}
          opacity={wallsOpacity * 0.8}
          strokeDasharray={4}
        />
        <line
          x1={520}
          y1={250}
          x2={550}
          y2={250}
          stroke="#4A90D9"
          strokeWidth={1}
          opacity={wallsOpacity * 0.8}
          strokeDasharray={4}
        />
      </svg>
    </AbsoluteFill>
  );
};
