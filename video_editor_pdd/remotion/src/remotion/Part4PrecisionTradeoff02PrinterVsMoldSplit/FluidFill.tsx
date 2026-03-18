import React, { useMemo } from 'react';
import { MOLD, COLORS } from './constants';

/**
 * Simulates organic fluid filling the injection mold cavity.
 * Uses layered blobs/ellipses to create a chaotic, organic fill look
 * that eventually conforms to the mold walls.
 */
export const FluidFill: React.FC<{
  fillProgress: number; // 0 to 1
}> = ({ fillProgress }) => {
  const { width, height, centerX, centerY } = MOLD;

  const left = centerX - width / 2;
  const top = centerY - height / 2;
  const right = left + width;
  const bottom = top + height;
  const gapWidth = 60;
  const halfGap = gapWidth / 2;

  // Interior bounds (inside the walls)
  const inLeft = left + 6;
  const inRight = right - 6;
  const inTop = top + 6;
  const inBottom = bottom - 6;
  const inWidth = inRight - inLeft;
  const inHeight = inBottom - inTop;

  // Generate pseudo-random blob positions for the fluid simulation
  // These create an organic, chaotic fill effect
  const blobs = useMemo(() => {
    const result: Array<{
      cx: number;
      cy: number;
      rx: number;
      ry: number;
      appearAt: number; // 0-1, when this blob appears
    }> = [];

    // Seed-based pseudo-random for deterministic rendering
    const seededRandom = (seed: number) => {
      const x = Math.sin(seed * 12.9898 + 78.233) * 43758.5453;
      return x - Math.floor(x);
    };

    // Stream entry point (top center)
    const entryX = centerX;
    const entryY = inTop;

    // Phase 1 (0-0.15): Stream flowing down from nozzle
    for (let i = 0; i < 8; i++) {
      const t = i / 8;
      result.push({
        cx: entryX + (seededRandom(i * 7 + 1) - 0.5) * 30,
        cy: entryY + t * inHeight * 0.5,
        rx: 15 + seededRandom(i * 3) * 20,
        ry: 20 + seededRandom(i * 5) * 15,
        appearAt: t * 0.15,
      });
    }

    // Phase 2 (0.15-0.5): Liquid spreads at bottom, hits walls
    for (let i = 0; i < 20; i++) {
      const t = i / 20;
      const yBias = 0.5 + t * 0.4; // favor bottom half
      result.push({
        cx: inLeft + seededRandom(i * 13 + 50) * inWidth,
        cy: entryY + yBias * inHeight,
        rx: 25 + seededRandom(i * 11 + 30) * 40,
        ry: 20 + seededRandom(i * 17 + 20) * 30,
        appearAt: 0.1 + t * 0.4,
      });
    }

    // Phase 3 (0.5-0.85): Fills remaining gaps, rising up
    for (let i = 0; i < 25; i++) {
      const t = i / 25;
      result.push({
        cx: inLeft + seededRandom(i * 23 + 100) * inWidth,
        cy: entryY + seededRandom(i * 29 + 110) * inHeight,
        rx: 30 + seededRandom(i * 19 + 120) * 50,
        ry: 25 + seededRandom(i * 31 + 130) * 40,
        appearAt: 0.4 + t * 0.45,
      });
    }

    // Phase 4 (0.85-1.0): Complete fill — large overlapping blobs
    for (let i = 0; i < 10; i++) {
      const t = i / 10;
      result.push({
        cx: inLeft + seededRandom(i * 37 + 200) * inWidth,
        cy: entryY + seededRandom(i * 41 + 210) * inHeight,
        rx: 60 + seededRandom(i * 43 + 220) * 60,
        ry: 50 + seededRandom(i * 47 + 230) * 50,
        appearAt: 0.75 + t * 0.25,
      });
    }

    return result;
  }, [centerX, inTop, inWidth, inHeight, inLeft]);

  // Clip path for the mold interior
  const clipId = 'mold-clip';

  return (
    <svg
      width={958}
      height={860}
      style={{ position: 'absolute', top: 60, left: 0, pointerEvents: 'none' }}
    >
      <defs>
        {/* Clip to mold interior */}
        <clipPath id={clipId}>
          <rect
            x={inLeft}
            y={inTop}
            width={inWidth}
            height={inHeight}
          />
        </clipPath>
      </defs>

      <g clipPath={`url(#${clipId})`}>
        {/* Fluid stream from nozzle */}
        {fillProgress > 0 && (
          <rect
            x={centerX - 8}
            y={inTop}
            width={16}
            height={Math.min(fillProgress * 3, 1) * inHeight}
            fill={COLORS.fluidColor}
            opacity={0.25}
            rx={8}
          />
        )}

        {/* Organic blobs */}
        {blobs.map((blob, i) => {
          if (fillProgress < blob.appearAt) return null;
          const localProgress = Math.min(
            1,
            (fillProgress - blob.appearAt) / 0.15
          );
          return (
            <ellipse
              key={i}
              cx={blob.cx}
              cy={blob.cy}
              rx={blob.rx * localProgress}
              ry={blob.ry * localProgress}
              fill={COLORS.fluidColor}
              opacity={0.2 * localProgress}
            />
          );
        })}

        {/* Final full fill overlay (appears near completion) */}
        {fillProgress > 0.85 && (
          <rect
            x={inLeft}
            y={inTop}
            width={inWidth}
            height={inHeight}
            fill={COLORS.fluidColor}
            opacity={0.2 * Math.min(1, (fillProgress - 0.85) / 0.15)}
            rx={2}
          />
        )}
      </g>
    </svg>
  );
};
