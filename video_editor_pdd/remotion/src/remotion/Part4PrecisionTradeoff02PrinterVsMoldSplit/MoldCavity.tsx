import React, { useMemo } from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  MOLD_WIDTH,
  MOLD_HEIGHT,
  MOLD_CENTER_X,
  MOLD_CENTER_Y,
  MOLD_WALL_WIDTH,
  WALL_COLOR,
  FLUID_COLOR,
  RIGHT_ACCENT,
  GRID_APPEAR_START,
  FLUID_START,
  FLUID_END,
} from './constants';

/**
 * Right panel: Injection mold cross-section with fluid fill animation.
 * Shows walls being drawn, then liquid flowing in and filling the cavity.
 */
export const MoldCavity: React.FC = () => {
  const frame = useCurrentFrame();

  // Mold rectangle bounds
  const moldLeft = MOLD_CENTER_X - MOLD_WIDTH / 2;
  const moldTop = MOLD_CENTER_Y - MOLD_HEIGHT / 2;
  const moldRight = moldLeft + MOLD_WIDTH;
  const moldBottom = moldTop + MOLD_HEIGHT;

  // Wall draw-in animation (frame 20-50)
  const wallProgress = interpolate(
    frame,
    [GRID_APPEAR_START, GRID_APPEAR_START + 30],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Wall perimeter: total length of the rectangle minus the gap at top-center (nozzle opening)
  const nozzleGap = 60; // gap for the nozzle opening at top

  // Fluid fill progress
  const fillProgress = interpolate(
    frame,
    [FLUID_START, FLUID_END],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Nozzle funnel
  const nozzleTopY = moldTop - 40;
  const nozzleFunnelWidth = 40;

  // Generate organic fluid blobs for the fill simulation
  const fluidBlobs = useMemo(() => {
    const blobs: Array<{
      cx: number;
      cy: number;
      rx: number;
      ry: number;
      delay: number;
      speed: number;
    }> = [];
    // Seed-based pseudo-random for deterministic animation
    const seed = (i: number) => {
      const x = Math.sin(i * 127.1 + 311.7) * 43758.5453;
      return x - Math.floor(x);
    };

    for (let i = 0; i < 30; i++) {
      const s1 = seed(i);
      const s2 = seed(i + 100);
      const s3 = seed(i + 200);
      blobs.push({
        cx: moldLeft + 20 + s1 * (MOLD_WIDTH - 40),
        cy: moldTop + 20 + s2 * (MOLD_HEIGHT - 40),
        rx: 30 + s3 * 60,
        ry: 20 + seed(i + 300) * 40,
        delay: s1 * 0.5,
        speed: 0.6 + s2 * 0.8,
      });
    }
    return blobs;
  }, [moldLeft, moldTop]);

  // Fluid drip from nozzle
  const dripProgress = interpolate(
    frame,
    [FLUID_START, FLUID_START + 40],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Fluid column from nozzle to pool
  const columnHeight = interpolate(
    frame,
    [FLUID_START, FLUID_START + 60],
    [0, MOLD_HEIGHT * 0.3],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Overall fill level (bottom-up)
  const fillHeight = fillProgress * MOLD_HEIGHT;

  return (
    <div style={{ position: 'absolute', top: 0, left: 0, width: 958, height: 1080 }}>
      <svg width={958} height={1080} viewBox="0 0 958 1080">
        {/* Clip path for mold interior */}
        <defs>
          <clipPath id="moldClip">
            <rect
              x={moldLeft + MOLD_WALL_WIDTH}
              y={moldTop + MOLD_WALL_WIDTH}
              width={MOLD_WIDTH - MOLD_WALL_WIDTH * 2}
              height={MOLD_HEIGHT - MOLD_WALL_WIDTH * 2}
            />
          </clipPath>
          {/* Gradient for fluid */}
          <radialGradient id="fluidGrad" cx="50%" cy="30%" r="70%">
            <stop offset="0%" stopColor={FLUID_COLOR} stopOpacity={0.35} />
            <stop offset="100%" stopColor={FLUID_COLOR} stopOpacity={0.15} />
          </radialGradient>
        </defs>

        {/* Nozzle funnel */}
        {wallProgress > 0 && (
          <g opacity={wallProgress * 0.5}>
            <polygon
              points={`
                ${MOLD_CENTER_X - nozzleFunnelWidth / 2},${nozzleTopY}
                ${MOLD_CENTER_X + nozzleFunnelWidth / 2},${nozzleTopY}
                ${MOLD_CENTER_X + nozzleGap / 2 - 5},${moldTop - 2}
                ${MOLD_CENTER_X - nozzleGap / 2 + 5},${moldTop - 2}
              `}
              fill="none"
              stroke="#94A3B8"
              strokeWidth={2}
            />
          </g>
        )}

        {/* Mold walls — drawn progressively */}
        {wallProgress > 0 && (
          <g>
            {/* Left wall */}
            <line
              x1={moldLeft}
              y1={moldTop}
              x2={moldLeft}
              y2={moldTop + (moldBottom - moldTop) * Math.min(wallProgress * 1.5, 1)}
              stroke={WALL_COLOR}
              strokeWidth={MOLD_WALL_WIDTH}
              opacity={0.8}
            />
            {/* Right wall */}
            <line
              x1={moldRight}
              y1={moldTop}
              x2={moldRight}
              y2={moldTop + (moldBottom - moldTop) * Math.min(wallProgress * 1.5, 1)}
              stroke={WALL_COLOR}
              strokeWidth={MOLD_WALL_WIDTH}
              opacity={0.8}
            />
            {/* Bottom wall */}
            <line
              x1={moldLeft}
              y1={moldBottom}
              x2={moldLeft + MOLD_WIDTH * Math.min(wallProgress * 2, 1)}
              y2={moldBottom}
              stroke={WALL_COLOR}
              strokeWidth={MOLD_WALL_WIDTH}
              opacity={0.8}
            />
            {/* Top wall (two segments with nozzle gap) */}
            <line
              x1={moldLeft}
              y1={moldTop}
              x2={moldLeft + (MOLD_CENTER_X - moldLeft - nozzleGap / 2) * Math.min(wallProgress * 2, 1)}
              y2={moldTop}
              stroke={WALL_COLOR}
              strokeWidth={MOLD_WALL_WIDTH}
              opacity={0.8}
            />
            <line
              x1={MOLD_CENTER_X + nozzleGap / 2}
              y1={moldTop}
              x2={MOLD_CENTER_X + nozzleGap / 2 + (moldRight - MOLD_CENTER_X - nozzleGap / 2) * Math.min(wallProgress * 2, 1)}
              y2={moldTop}
              stroke={WALL_COLOR}
              strokeWidth={MOLD_WALL_WIDTH}
              opacity={0.8}
            />

            {/* Wall labels */}
            {wallProgress > 0.5 && (
              <g opacity={(wallProgress - 0.5) * 2}>
                {/* Left wall label */}
                <text
                  x={moldLeft - 14}
                  y={MOLD_CENTER_Y}
                  fill={WALL_COLOR}
                  opacity={0.4}
                  fontSize={8}
                  fontFamily="Inter, sans-serif"
                  textAnchor="middle"
                  transform={`rotate(-90, ${moldLeft - 14}, ${MOLD_CENTER_Y})`}
                >
                  WALL
                </text>
                {/* Right wall label */}
                <text
                  x={moldRight + 14}
                  y={MOLD_CENTER_Y}
                  fill={WALL_COLOR}
                  opacity={0.4}
                  fontSize={8}
                  fontFamily="Inter, sans-serif"
                  textAnchor="middle"
                  transform={`rotate(90, ${moldRight + 14}, ${MOLD_CENTER_Y})`}
                >
                  WALL
                </text>
                {/* Bottom wall label */}
                <text
                  x={MOLD_CENTER_X}
                  y={moldBottom + 16}
                  fill={WALL_COLOR}
                  opacity={0.4}
                  fontSize={8}
                  fontFamily="Inter, sans-serif"
                  textAnchor="middle"
                >
                  WALL
                </text>
                {/* Top wall label */}
                <text
                  x={moldLeft + 40}
                  y={moldTop - 8}
                  fill={WALL_COLOR}
                  opacity={0.4}
                  fontSize={8}
                  fontFamily="Inter, sans-serif"
                  textAnchor="middle"
                >
                  WALL
                </text>
              </g>
            )}
          </g>
        )}

        {/* Fluid fill — clipped to mold interior */}
        {fillProgress > 0 && (
          <g clipPath="url(#moldClip)">
            {/* Stream from nozzle */}
            {dripProgress > 0 && fillProgress < 0.95 && (
              <rect
                x={MOLD_CENTER_X - 4}
                y={moldTop}
                width={8}
                height={columnHeight}
                fill={FLUID_COLOR}
                opacity={0.3}
                rx={4}
              />
            )}

            {/* Main fill level (rising from bottom) */}
            <rect
              x={moldLeft + MOLD_WALL_WIDTH}
              y={moldBottom - fillHeight}
              width={MOLD_WIDTH - MOLD_WALL_WIDTH * 2}
              height={fillHeight}
              fill={FLUID_COLOR}
              opacity={0.2}
            />

            {/* Organic blobs for chaotic fluid look */}
            {fluidBlobs.map((blob, i) => {
              const blobFill = interpolate(
                fillProgress,
                [blob.delay, blob.delay + blob.speed],
                [0, 1],
                { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
              );
              if (blobFill <= 0) return null;

              // Blob rises from bottom, so invert Y based on fill progress
              const blobY = moldBottom - blobFill * (moldBottom - blob.cy);

              return (
                <ellipse
                  key={i}
                  cx={blob.cx}
                  cy={blobY}
                  rx={blob.rx * blobFill}
                  ry={blob.ry * blobFill}
                  fill="url(#fluidGrad)"
                  opacity={blobFill * 0.6}
                />
              );
            })}

            {/* Surface meniscus / wave at top of fluid */}
            {fillProgress > 0.05 && (
              <ellipse
                cx={MOLD_CENTER_X}
                cy={moldBottom - fillHeight}
                rx={(MOLD_WIDTH - MOLD_WALL_WIDTH * 2) / 2}
                ry={6 + Math.sin(frame * 0.15) * 3}
                fill={FLUID_COLOR}
                opacity={0.25}
              />
            )}
          </g>
        )}
      </svg>

      {/* Counter */}
      <div
        style={{
          position: 'absolute',
          bottom: 180,
          left: 0,
          width: '100%',
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          color: RIGHT_ACCENT,
        }}
      >
        Walls defined: 4
      </div>

      {/* Annotation */}
      <div
        style={{
          position: 'absolute',
          bottom: 150,
          left: 0,
          width: '100%',
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 11,
          color: RIGHT_ACCENT,
          opacity: 0.4,
        }}
      >
        Precision comes from the walls
      </div>
    </div>
  );
};

export default MoldCavity;
