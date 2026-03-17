import React from 'react';
import {
  CENTER_X,
  CENTER_Y,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  CAVITY_WIDTH,
  CAVITY_HEIGHT,
  NOZZLE_TOP_WIDTH,
  NOZZLE_BOTTOM_WIDTH,
  NOZZLE_HEIGHT,
  SHELL_COLOR,
  SHELL_OPACITY,
  SHELL_STROKE,
  CAVITY_BG_COLOR,
  CAVITY_BG_OPACITY,
  AMBER,
  BLUE,
  GREEN,
} from './constants';

interface MoldShapeProps {
  drawProgress: number; // 0..1 how much of the outline is drawn
  wallOpacity: number; // amber wall highlight
  nozzleOpacity: number; // blue nozzle highlight
  cavityFillProgress: number; // 0..1 green fill bottom-up
  cavityFillOpacity: number; // green fill max opacity
}

export const MoldShape: React.FC<MoldShapeProps> = ({
  drawProgress,
  wallOpacity,
  nozzleOpacity,
  cavityFillProgress,
  cavityFillOpacity,
}) => {
  const left = CENTER_X - MOLD_WIDTH / 2;
  const top = CENTER_Y - MOLD_HEIGHT / 2;
  const cavityLeft = CENTER_X - CAVITY_WIDTH / 2;
  const cavityTop = CENTER_Y - CAVITY_HEIGHT / 2;

  // Nozzle coordinates
  const nozzleTopLeft = CENTER_X - NOZZLE_TOP_WIDTH / 2;
  const nozzleTopRight = CENTER_X + NOZZLE_TOP_WIDTH / 2;
  const nozzleBottomLeft = CENTER_X - NOZZLE_BOTTOM_WIDTH / 2;
  const nozzleBottomRight = CENTER_X + NOZZLE_BOTTOM_WIDTH / 2;
  const nozzleTopY = top - NOZZLE_HEIGHT;
  const nozzleBottomY = top;

  // Outer shell path (rounded rect approximation)
  const r = 16; // corner radius
  const shellPath = `
    M ${left + r} ${top}
    L ${left + MOLD_WIDTH - r} ${top}
    Q ${left + MOLD_WIDTH} ${top} ${left + MOLD_WIDTH} ${top + r}
    L ${left + MOLD_WIDTH} ${top + MOLD_HEIGHT - r}
    Q ${left + MOLD_WIDTH} ${top + MOLD_HEIGHT} ${left + MOLD_WIDTH - r} ${top + MOLD_HEIGHT}
    L ${left + r} ${top + MOLD_HEIGHT}
    Q ${left} ${top + MOLD_HEIGHT} ${left} ${top + MOLD_HEIGHT - r}
    L ${left} ${top + r}
    Q ${left} ${top} ${left + r} ${top}
    Z
  `;

  // Cavity path (inner rect)
  const cr = 8;
  const cavityPath = `
    M ${cavityLeft + cr} ${cavityTop}
    L ${cavityLeft + CAVITY_WIDTH - cr} ${cavityTop}
    Q ${cavityLeft + CAVITY_WIDTH} ${cavityTop} ${cavityLeft + CAVITY_WIDTH} ${cavityTop + cr}
    L ${cavityLeft + CAVITY_WIDTH} ${cavityTop + CAVITY_HEIGHT - cr}
    Q ${cavityLeft + CAVITY_WIDTH} ${cavityTop + CAVITY_HEIGHT} ${cavityLeft + CAVITY_WIDTH - cr} ${cavityTop + CAVITY_HEIGHT}
    L ${cavityLeft + cr} ${cavityTop + CAVITY_HEIGHT}
    Q ${cavityLeft} ${cavityTop + CAVITY_HEIGHT} ${cavityLeft} ${cavityTop + CAVITY_HEIGHT - cr}
    L ${cavityLeft} ${cavityTop + cr}
    Q ${cavityLeft} ${cavityTop} ${cavityLeft + cr} ${cavityTop}
    Z
  `;

  // Nozzle path (tapered funnel)
  const nozzlePath = `
    M ${nozzleTopLeft} ${nozzleTopY}
    L ${nozzleTopRight} ${nozzleTopY}
    L ${nozzleBottomRight} ${nozzleBottomY}
    L ${nozzleBottomLeft} ${nozzleBottomY}
    Z
  `;

  // Approximate path lengths for stroke-dashoffset animation
  const shellPerimeter = 2 * (MOLD_WIDTH + MOLD_HEIGHT);
  const cavityPerimeter = 2 * (CAVITY_WIDTH + CAVITY_HEIGHT);
  const nozzlePerimeter = 2 * (NOZZLE_TOP_WIDTH + NOZZLE_HEIGHT) + 60;

  // Draw phases: shell 0-0.5, cavity 0.5-0.8, nozzle 0.8-1.0
  const shellDraw = Math.min(1, drawProgress / 0.5);
  const cavityDraw = Math.min(1, Math.max(0, (drawProgress - 0.5) / 0.3));
  const nozzleDraw = Math.min(1, Math.max(0, (drawProgress - 0.8) / 0.2));

  // Green fill clip: bottom-up
  const cavityBottom = cavityTop + CAVITY_HEIGHT;
  const fillHeight = CAVITY_HEIGHT * cavityFillProgress;
  const fillTop = cavityBottom - fillHeight;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        {/* Glow filters */}
        <filter id="amber-glow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="12" result="blur" />
          <feFlood floodColor={AMBER} floodOpacity={0.15} result="color" />
          <feComposite in="color" in2="blur" operator="in" />
        </filter>
        <filter id="blue-glow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="12" result="blur" />
          <feFlood floodColor={BLUE} floodOpacity={0.15} result="color" />
          <feComposite in="color" in2="blur" operator="in" />
        </filter>
        <filter id="green-glow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="8" result="blur" />
          <feFlood floodColor={GREEN} floodOpacity={0.1} result="color" />
          <feComposite in="color" in2="blur" operator="in" />
        </filter>

        {/* Clip path for cavity fill */}
        <clipPath id="cavity-clip">
          <rect
            x={cavityLeft}
            y={cavityTop}
            width={CAVITY_WIDTH}
            height={CAVITY_HEIGHT}
            rx={cr}
          />
        </clipPath>

        {/* Green gradient for cavity fill */}
        <linearGradient id="green-fill" x1="0" y1="1" x2="0" y2="0">
          <stop offset="0%" stopColor={GREEN} stopOpacity={cavityFillOpacity} />
          <stop
            offset="100%"
            stopColor={GREEN}
            stopOpacity={cavityFillOpacity * 0.5}
          />
        </linearGradient>
      </defs>

      {/* ── Cavity background fill ── */}
      <path
        d={cavityPath}
        fill={CAVITY_BG_COLOR}
        opacity={CAVITY_BG_OPACITY * drawProgress}
      />

      {/* ── Green cavity fill (bottom-up) ── */}
      {cavityFillProgress > 0 && (
        <g clipPath="url(#cavity-clip)">
          <rect
            x={cavityLeft}
            y={fillTop}
            width={CAVITY_WIDTH}
            height={fillHeight}
            fill="url(#green-fill)"
          />
          {/* Organic texture: subtle noise rectangles */}
          {Array.from({ length: 12 }).map((_, i) => {
            const nx =
              cavityLeft + ((i * 137.5) % CAVITY_WIDTH);
            const ny =
              fillTop + ((i * 89.3) % Math.max(fillHeight, 1));
            return (
              <rect
                key={`noise-${i}`}
                x={nx}
                y={ny}
                width={40 + (i % 3) * 20}
                height={30 + (i % 4) * 15}
                fill={GREEN}
                opacity={0.06 * cavityFillProgress}
                rx={4}
              />
            );
          })}
          {/* Green glow overlay */}
          <rect
            x={cavityLeft}
            y={fillTop}
            width={CAVITY_WIDTH}
            height={fillHeight}
            fill={GREEN}
            opacity={0.05 * cavityFillProgress}
            filter="url(#green-glow)"
          />
        </g>
      )}

      {/* ── Amber wall highlights ── */}
      {wallOpacity > 0 && (
        <g opacity={wallOpacity}>
          {/* Glow layer */}
          <path
            d={cavityPath}
            fill="none"
            stroke={AMBER}
            strokeWidth={8}
            filter="url(#amber-glow)"
          />
          {/* Wall stroke */}
          <path
            d={cavityPath}
            fill="none"
            stroke={AMBER}
            strokeWidth={4}
            opacity={0.5}
          />
        </g>
      )}

      {/* ── Outer shell ── */}
      <path
        d={shellPath}
        fill="none"
        stroke={SHELL_COLOR}
        strokeWidth={SHELL_STROKE}
        opacity={SHELL_OPACITY}
        strokeDasharray={shellPerimeter}
        strokeDashoffset={shellPerimeter * (1 - shellDraw)}
      />

      {/* ── Cavity outline ── */}
      <path
        d={cavityPath}
        fill="none"
        stroke={SHELL_COLOR}
        strokeWidth={2}
        opacity={SHELL_OPACITY * 0.5}
        strokeDasharray={cavityPerimeter}
        strokeDashoffset={cavityPerimeter * (1 - cavityDraw)}
      />

      {/* ── Nozzle ── */}
      <g>
        {/* Base nozzle outline */}
        <path
          d={nozzlePath}
          fill="none"
          stroke={SHELL_COLOR}
          strokeWidth={SHELL_STROKE}
          opacity={SHELL_OPACITY}
          strokeDasharray={nozzlePerimeter}
          strokeDashoffset={nozzlePerimeter * (1 - nozzleDraw)}
        />
        {/* Blue nozzle highlight */}
        {nozzleOpacity > 0 && (
          <g opacity={nozzleOpacity}>
            <path
              d={nozzlePath}
              fill="none"
              stroke={BLUE}
              strokeWidth={6}
              filter="url(#blue-glow)"
            />
            <path
              d={nozzlePath}
              fill={BLUE}
              opacity={0.08}
            />
            <path
              d={nozzlePath}
              fill="none"
              stroke={BLUE}
              strokeWidth={3}
              opacity={0.5}
            />
          </g>
        )}
      </g>

      {/* ── Dimension lines (decorative engineering detail) ── */}
      <g opacity={0.15 * drawProgress}>
        {/* Horizontal dimension at bottom */}
        <line
          x1={left}
          y1={top + MOLD_HEIGHT + 30}
          x2={left + MOLD_WIDTH}
          y2={top + MOLD_HEIGHT + 30}
          stroke={SHELL_COLOR}
          strokeWidth={1}
        />
        <line
          x1={left}
          y1={top + MOLD_HEIGHT + 20}
          x2={left}
          y2={top + MOLD_HEIGHT + 40}
          stroke={SHELL_COLOR}
          strokeWidth={1}
        />
        <line
          x1={left + MOLD_WIDTH}
          y1={top + MOLD_HEIGHT + 20}
          x2={left + MOLD_WIDTH}
          y2={top + MOLD_HEIGHT + 40}
          stroke={SHELL_COLOR}
          strokeWidth={1}
        />
        {/* Vertical dimension on right */}
        <line
          x1={left + MOLD_WIDTH + 30}
          y1={top}
          x2={left + MOLD_WIDTH + 30}
          y2={top + MOLD_HEIGHT}
          stroke={SHELL_COLOR}
          strokeWidth={1}
        />
        <line
          x1={left + MOLD_WIDTH + 20}
          y1={top}
          x2={left + MOLD_WIDTH + 40}
          y2={top}
          stroke={SHELL_COLOR}
          strokeWidth={1}
        />
        <line
          x1={left + MOLD_WIDTH + 20}
          y1={top + MOLD_HEIGHT}
          x2={left + MOLD_WIDTH + 40}
          y2={top + MOLD_HEIGHT}
          stroke={SHELL_COLOR}
          strokeWidth={1}
        />
      </g>
    </svg>
  );
};
