import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  MOLD_CX,
  MOLD_CY,
  MOLD_W,
  MOLD_H,
  CAVITY_W,
  CAVITY_H,
  NOZZLE_TOP_W,
  NOZZLE_BOT_W,
  NOZZLE_H,
  AMBER,
  BLUE,
  GREEN,
  WALLS_START,
  WALLS_ILLUM_DUR,
  NOZZLE_START,
  NOZZLE_ILLUM_DUR,
  CAVITY_START,
  CAVITY_FILL_DUR,
  ALL_BRIGHT_START,
  ALL_BRIGHT_DUR,
  WIDTH,
  HEIGHT,
} from './constants';

/**
 * Handles the sequential region illumination:
 *  1. Walls glow amber
 *  2. Nozzle glows blue (walls dim)
 *  3. Cavity fills green (nozzle dims)
 *  4. All re-illuminate
 */
export const RegionHighlight: React.FC = () => {
  const frame = useCurrentFrame();

  // Shell geometry
  const shellLeft = MOLD_CX - MOLD_W / 2;
  const shellTop = MOLD_CY - MOLD_H / 2;

  // Cavity geometry
  const cavLeft = MOLD_CX - CAVITY_W / 2;
  const cavTop = MOLD_CY - CAVITY_H / 2 + 30;

  // Nozzle geometry
  const nozTopY = shellTop - 10;
  const nozBotY = nozTopY + NOZZLE_H;
  const nozTL = MOLD_CX - NOZZLE_TOP_W / 2;
  const nozTR = MOLD_CX + NOZZLE_TOP_W / 2;
  const nozBL = MOLD_CX - NOZZLE_BOT_W / 2;
  const nozBR = MOLD_CX + NOZZLE_BOT_W / 2;

  // ── Wall illumination ────────────────────────────────────
  const wallsOn = interpolate(frame, [WALLS_START, WALLS_START + WALLS_ILLUM_DUR], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Walls dim when nozzle activates, re-brighten at ALL_BRIGHT_START
  const wallsDim = interpolate(
    frame,
    [NOZZLE_START, NOZZLE_START + 15, ALL_BRIGHT_START, ALL_BRIGHT_START + ALL_BRIGHT_DUR],
    [1, 0.3, 0.3, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  const wallOpacity = wallsOn * wallsDim;

  // ── Nozzle illumination ──────────────────────────────────
  const nozzleOn = interpolate(frame, [NOZZLE_START, NOZZLE_START + NOZZLE_ILLUM_DUR], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const nozzleDim = interpolate(
    frame,
    [CAVITY_START, CAVITY_START + 15, ALL_BRIGHT_START, ALL_BRIGHT_START + ALL_BRIGHT_DUR],
    [1, 0.3, 0.3, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  const nozzleOpacity = nozzleOn * nozzleDim;

  // ── Cavity fill ──────────────────────────────────────────
  const cavityFill = interpolate(frame, [CAVITY_START, CAVITY_START + CAVITY_FILL_DUR], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.bezier(0.25, 0.1, 0.25, 1)),
  });

  const cavityDim = interpolate(
    frame,
    [ALL_BRIGHT_START, ALL_BRIGHT_START + ALL_BRIGHT_DUR],
    [1, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  const cavityOpacity = cavityFill * cavityDim;

  // Bottom-up fill: clip from bottom rising upward
  const fillHeight = CAVITY_H * cavityFill;
  const fillTop = cavTop + CAVITY_H - fillHeight;

  // Wall segments: four inner walls of the cavity
  const wallStrokeWidth = 4;

  // Nozzle path
  const nozzlePath = `
    M ${nozTL},${nozTopY}
    H ${nozTR}
    L ${nozBR},${nozBotY}
    H ${nozBL}
    Z
  `;

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        {/* Amber glow */}
        <filter id="amber-glow" x="-30%" y="-30%" width="160%" height="160%">
          <feGaussianBlur stdDeviation="12" result="blur" />
          <feFlood floodColor={AMBER} floodOpacity="0.15" result="color" />
          <feComposite in="color" in2="blur" operator="in" result="glow" />
          <feMerge>
            <feMergeNode in="glow" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>

        {/* Blue glow */}
        <filter id="blue-glow" x="-30%" y="-30%" width="160%" height="160%">
          <feGaussianBlur stdDeviation="12" result="blur" />
          <feFlood floodColor={BLUE} floodOpacity="0.15" result="color" />
          <feComposite in="color" in2="blur" operator="in" result="glow" />
          <feMerge>
            <feMergeNode in="glow" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>

        {/* Green gradient for cavity fill — bottom-up */}
        <linearGradient id="green-fill" x1="0" y1="1" x2="0" y2="0">
          <stop offset="0%" stopColor={GREEN} stopOpacity="0.15" />
          <stop offset="100%" stopColor={GREEN} stopOpacity="0.08" />
        </linearGradient>

        {/* Clip for bottom-up fill */}
        <clipPath id="cavity-clip">
          <rect x={cavLeft} y={fillTop} width={CAVITY_W} height={fillHeight} />
        </clipPath>
      </defs>

      {/* ── Region 1: Wall segments (amber) ─────────────── */}
      <g opacity={wallOpacity} filter="url(#amber-glow)">
        {/* Left wall */}
        <line
          x1={cavLeft}
          y1={cavTop}
          x2={cavLeft}
          y2={cavTop + CAVITY_H}
          stroke={AMBER}
          strokeWidth={wallStrokeWidth}
          opacity={0.5}
        />
        {/* Right wall */}
        <line
          x1={cavLeft + CAVITY_W}
          y1={cavTop}
          x2={cavLeft + CAVITY_W}
          y2={cavTop + CAVITY_H}
          stroke={AMBER}
          strokeWidth={wallStrokeWidth}
          opacity={0.5}
        />
        {/* Bottom wall */}
        <line
          x1={cavLeft}
          y1={cavTop + CAVITY_H}
          x2={cavLeft + CAVITY_W}
          y2={cavTop + CAVITY_H}
          stroke={AMBER}
          strokeWidth={wallStrokeWidth}
          opacity={0.5}
        />
        {/* Top wall (partial — leaving gap for nozzle) */}
        <line
          x1={cavLeft}
          y1={cavTop}
          x2={MOLD_CX - NOZZLE_BOT_W / 2 - 5}
          y2={cavTop}
          stroke={AMBER}
          strokeWidth={wallStrokeWidth}
          opacity={0.5}
        />
        <line
          x1={MOLD_CX + NOZZLE_BOT_W / 2 + 5}
          y1={cavTop}
          x2={cavLeft + CAVITY_W}
          y2={cavTop}
          stroke={AMBER}
          strokeWidth={wallStrokeWidth}
          opacity={0.5}
        />
      </g>

      {/* ── Region 2: Nozzle (blue) ─────────────────────── */}
      <g opacity={nozzleOpacity} filter="url(#blue-glow)">
        <path
          d={nozzlePath}
          fill="none"
          stroke={BLUE}
          strokeWidth={3}
          opacity={0.5}
        />
        {/* Inner channel line */}
        <line
          x1={MOLD_CX}
          y1={nozTopY + 8}
          x2={MOLD_CX}
          y2={nozBotY - 4}
          stroke={BLUE}
          strokeWidth={1.5}
          opacity={0.3}
          strokeDasharray="4 4"
        />
      </g>

      {/* ── Region 3: Cavity fill (green, bottom-up) ────── */}
      <g opacity={cavityOpacity} clipPath="url(#cavity-clip)">
        <rect
          x={cavLeft}
          y={cavTop}
          width={CAVITY_W}
          height={CAVITY_H}
          fill="url(#green-fill)"
        />
        {/* Subtle organic texture — horizontal wave lines */}
        {Array.from({ length: 12 }).map((_, i) => {
          const lineY = cavTop + (CAVITY_H / 12) * (i + 0.5);
          const amp = 3 + (i % 3) * 2;
          return (
            <path
              key={`wave-${i}`}
              d={`M ${cavLeft + 10},${lineY} Q ${cavLeft + CAVITY_W * 0.25},${lineY - amp} ${cavLeft + CAVITY_W * 0.5},${lineY} Q ${cavLeft + CAVITY_W * 0.75},${lineY + amp} ${cavLeft + CAVITY_W - 10},${lineY}`}
              fill="none"
              stroke={GREEN}
              strokeWidth={0.5}
              opacity={0.06}
            />
          );
        })}
      </g>
    </svg>
  );
};
