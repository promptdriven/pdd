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
  SHELL_COLOR,
  SHELL_OPACITY,
  SHELL_STROKE,
  CAVITY_BG,
  CAVITY_BG_OPACITY,
  DRAW_END,
  WIDTH,
  HEIGHT,
} from './constants';

/**
 * Draws the mold outline (outer shell + cavity + nozzle) with a
 * stroke-dashoffset reveal animation over the first DRAW_END frames.
 */
export const MoldShape: React.FC = () => {
  const frame = useCurrentFrame();

  // Progress 0→1 over draw phase
  const drawProgress = interpolate(frame, [0, DRAW_END], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.ease),
  });

  // ── Outer shell path (rounded rect) ──────────────────────
  const shellLeft = MOLD_CX - MOLD_W / 2;
  const shellTop = MOLD_CY - MOLD_H / 2;
  const r = 16; // rounded industrial corners

  const outerPath = `
    M ${shellLeft + r},${shellTop}
    H ${shellLeft + MOLD_W - r}
    Q ${shellLeft + MOLD_W},${shellTop} ${shellLeft + MOLD_W},${shellTop + r}
    V ${shellTop + MOLD_H - r}
    Q ${shellLeft + MOLD_W},${shellTop + MOLD_H} ${shellLeft + MOLD_W - r},${shellTop + MOLD_H}
    H ${shellLeft + r}
    Q ${shellLeft},${shellTop + MOLD_H} ${shellLeft},${shellTop + MOLD_H - r}
    V ${shellTop + r}
    Q ${shellLeft},${shellTop} ${shellLeft + r},${shellTop}
    Z
  `;
  const outerLen = 2 * (MOLD_W + MOLD_H); // approximate perimeter

  // ── Cavity path (inner rect) ─────────────────────────────
  const cavLeft = MOLD_CX - CAVITY_W / 2;
  const cavTop = MOLD_CY - CAVITY_H / 2 + 30; // slight downward offset for nozzle space

  const cavityPath = `
    M ${cavLeft},${cavTop}
    H ${cavLeft + CAVITY_W}
    V ${cavTop + CAVITY_H}
    H ${cavLeft}
    Z
  `;
  const cavityLen = 2 * (CAVITY_W + CAVITY_H);

  // ── Nozzle path (tapered funnel) ─────────────────────────
  const nozTopY = shellTop - 10; // slightly above the shell
  const nozBotY = nozTopY + NOZZLE_H;
  const nozTL = MOLD_CX - NOZZLE_TOP_W / 2;
  const nozTR = MOLD_CX + NOZZLE_TOP_W / 2;
  const nozBL = MOLD_CX - NOZZLE_BOT_W / 2;
  const nozBR = MOLD_CX + NOZZLE_BOT_W / 2;

  const nozzlePath = `
    M ${nozTL},${nozTopY}
    H ${nozTR}
    L ${nozBR},${nozBotY}
    H ${nozBL}
    Z
  `;
  const nozzleLen = NOZZLE_TOP_W + 2 * Math.hypot(NOZZLE_H, (NOZZLE_TOP_W - NOZZLE_BOT_W) / 2) + NOZZLE_BOT_W;

  // Phase staggering: outer 0-0.5, cavity 0.3-0.7, nozzle 0.5-1.0
  const outerDraw = interpolate(drawProgress, [0, 0.5], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });
  const cavityDraw = interpolate(drawProgress, [0.3, 0.7], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });
  const nozzleDraw = interpolate(drawProgress, [0.5, 1.0], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        {/* Glow filter for the shell */}
        <filter id="shell-glow" x="-20%" y="-20%" width="140%" height="140%">
          <feGaussianBlur stdDeviation="4" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Outer shell */}
      <path
        d={outerPath}
        fill="none"
        stroke={SHELL_COLOR}
        strokeWidth={SHELL_STROKE}
        opacity={SHELL_OPACITY}
        strokeDasharray={outerLen}
        strokeDashoffset={outerLen * (1 - outerDraw)}
        filter="url(#shell-glow)"
      />

      {/* Cavity interior background */}
      <path
        d={cavityPath}
        fill={CAVITY_BG}
        fillOpacity={CAVITY_BG_OPACITY * cavityDraw}
        stroke={SHELL_COLOR}
        strokeWidth={1.5}
        strokeOpacity={SHELL_OPACITY * cavityDraw}
        strokeDasharray={cavityLen}
        strokeDashoffset={cavityLen * (1 - cavityDraw)}
      />

      {/* Nozzle */}
      <path
        d={nozzlePath}
        fill="none"
        stroke={SHELL_COLOR}
        strokeWidth={SHELL_STROKE}
        opacity={SHELL_OPACITY * nozzleDraw}
        strokeDasharray={nozzleLen}
        strokeDashoffset={nozzleLen * (1 - nozzleDraw)}
      />

      {/* Dimension lines — subtle engineering feel */}
      <g opacity={0.12 * drawProgress}>
        {/* Horizontal dimension across top */}
        <line
          x1={shellLeft}
          y1={shellTop - 30}
          x2={shellLeft + MOLD_W}
          y2={shellTop - 30}
          stroke={SHELL_COLOR}
          strokeWidth={0.5}
        />
        <line x1={shellLeft} y1={shellTop - 35} x2={shellLeft} y2={shellTop - 25} stroke={SHELL_COLOR} strokeWidth={0.5} />
        <line x1={shellLeft + MOLD_W} y1={shellTop - 35} x2={shellLeft + MOLD_W} y2={shellTop - 25} stroke={SHELL_COLOR} strokeWidth={0.5} />

        {/* Vertical dimension along right */}
        <line
          x1={shellLeft + MOLD_W + 30}
          y1={shellTop}
          x2={shellLeft + MOLD_W + 30}
          y2={shellTop + MOLD_H}
          stroke={SHELL_COLOR}
          strokeWidth={0.5}
        />
        <line x1={shellLeft + MOLD_W + 25} y1={shellTop} x2={shellLeft + MOLD_W + 35} y2={shellTop} stroke={SHELL_COLOR} strokeWidth={0.5} />
        <line x1={shellLeft + MOLD_W + 25} y1={shellTop + MOLD_H} x2={shellLeft + MOLD_W + 35} y2={shellTop + MOLD_H} stroke={SHELL_COLOR} strokeWidth={0.5} />
      </g>
    </svg>
  );
};
