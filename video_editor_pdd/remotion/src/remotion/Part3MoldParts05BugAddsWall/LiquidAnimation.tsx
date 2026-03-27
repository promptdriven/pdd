import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  MOLD_X,
  MOLD_Y,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  MOLD_WALL_THICKNESS,
  NOZZLE_X,
  NOZZLE_Y,
  EXISTING_WALLS,
  NEW_WALL,
  LIQUID_CYAN,
  LIQUID_TEAL,
  LIQUID_DRAIN_START,
  LIQUID_DRAIN_DURATION,
  LIQUID_REFILL_START,
  LIQUID_REFILL_DURATION,
  WALL_SLIDE_START,
  WALL_SLIDE_DURATION,
} from './constants';

/**
 * Handles both the initial liquid fill (visible from frame 0),
 * the drain animation, and the refill animation.
 */
export const LiquidAnimation: React.FC = () => {
  const frame = useCurrentFrame();

  // Cavity interior bounds
  const cavityLeft = MOLD_X + MOLD_WALL_THICKNESS;
  const cavityTop = MOLD_Y + MOLD_WALL_THICKNESS;
  const cavityWidth = MOLD_WIDTH - 2 * MOLD_WALL_THICKNESS;
  const cavityHeight = MOLD_HEIGHT - 2 * MOLD_WALL_THICKNESS;

  // Phase 1: Initial liquid (visible from frame 0 until drain)
  // Phase 2: Drain (frames 180-200)
  // Phase 3: Refill (frames 210-250)
  // Phase 4: New liquid stable

  const isDraining = frame >= LIQUID_DRAIN_START && frame < LIQUID_DRAIN_START + LIQUID_DRAIN_DURATION;
  const isDrained = frame >= LIQUID_DRAIN_START + LIQUID_DRAIN_DURATION && frame < LIQUID_REFILL_START;
  const isRefilling = frame >= LIQUID_REFILL_START && frame < LIQUID_REFILL_START + LIQUID_REFILL_DURATION;
  const isRefilled = frame >= LIQUID_REFILL_START + LIQUID_REFILL_DURATION;
  const isInitialFill = frame < LIQUID_DRAIN_START;

  // Has the new wall arrived?
  const wallArrived = frame >= WALL_SLIDE_START + WALL_SLIDE_DURATION;

  // Drain progress (top-to-bottom: liquid level drops)
  const drainProgress = isDraining
    ? interpolate(
        frame,
        [LIQUID_DRAIN_START, LIQUID_DRAIN_START + LIQUID_DRAIN_DURATION],
        [0, 1],
        { easing: Easing.in(Easing.quad), extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
      )
    : 0;

  // Refill progress (from nozzle, fills top-to-bottom)
  const refillProgress = isRefilling
    ? interpolate(
        frame,
        [LIQUID_REFILL_START, LIQUID_REFILL_START + LIQUID_REFILL_DURATION],
        [0, 1],
        { easing: Easing.bezier(0.25, 0.1, 0.25, 1), extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
      )
    : 0;

  // Calculate liquid visibility and clip
  let liquidOpacity = 0;
  let liquidClipTop = cavityTop;
  let liquidClipHeight = cavityHeight;
  let useRefillGradient = false;

  if (isInitialFill) {
    liquidOpacity = 0.55;
    liquidClipTop = cavityTop;
    liquidClipHeight = cavityHeight;
  } else if (isDraining) {
    liquidOpacity = interpolate(drainProgress, [0, 1], [0.55, 0]);
    // Liquid level drops: clip from top
    liquidClipTop = cavityTop + drainProgress * cavityHeight * 0.5;
    liquidClipHeight = cavityHeight - drainProgress * cavityHeight;
  } else if (isDrained) {
    liquidOpacity = 0;
  } else if (isRefilling) {
    liquidOpacity = interpolate(refillProgress, [0, 0.2, 1], [0, 0.55, 0.6], {
      extrapolateRight: 'clamp',
    });
    // Fill from top
    liquidClipTop = cavityTop;
    liquidClipHeight = cavityHeight * refillProgress;
    useRefillGradient = true;
  } else if (isRefilled) {
    liquidOpacity = 0.6;
    useRefillGradient = true;
  }

  if (liquidOpacity <= 0) return null;

  // Build wall cutout clip paths
  const allWalls = wallArrived ? [...EXISTING_WALLS, NEW_WALL] : EXISTING_WALLS;

  // Nozzle stream during refill
  const showNozzleStream = isRefilling && refillProgress > 0.05 && refillProgress < 0.9;
  const nozzleStreamOpacity = showNozzleStream
    ? interpolate(refillProgress, [0.05, 0.15, 0.8, 0.9], [0, 0.7, 0.7, 0], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      })
    : 0;

  const clipId = wallArrived ? 'liquidClipNew' : 'liquidClipOld';
  const gradientId = useRefillGradient ? 'liquidGradNew' : 'liquidGradOld';

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        {/* Liquid gradient — initial */}
        <linearGradient id="liquidGradOld" x1="0" y1="0" x2="1" y2="1">
          <stop offset="0%" stopColor={LIQUID_CYAN} />
          <stop offset="100%" stopColor={LIQUID_TEAL} />
        </linearGradient>

        {/* Liquid gradient — refill (slightly shifted hue) */}
        <linearGradient id="liquidGradNew" x1="0" y1="0" x2="1" y2="1">
          <stop offset="0%" stopColor={LIQUID_CYAN} />
          <stop offset="60%" stopColor={LIQUID_TEAL} />
          <stop offset="100%" stopColor="#0F766E" />
        </linearGradient>

        {/* Clip path that excludes walls from the liquid */}
        <clipPath id={clipId}>
          <rect
            x={cavityLeft}
            y={liquidClipTop}
            width={cavityWidth}
            height={liquidClipHeight}
          />
        </clipPath>

        <filter id="liquidGlow" x="-10%" y="-10%" width="120%" height="120%">
          <feGaussianBlur stdDeviation="3" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Main liquid fill */}
      <g clipPath={`url(#${clipId})`}>
        <rect
          x={cavityLeft}
          y={liquidClipTop}
          width={cavityWidth}
          height={liquidClipHeight}
          fill={`url(#${gradientId})`}
          opacity={liquidOpacity}
          filter="url(#liquidGlow)"
        />
        {/* Cut out wall shapes from liquid (draw dark rects over wall positions) */}
        {allWalls.map((wall, i) => (
          <rect
            key={`wall-cutout-${i}`}
            x={wall.x - 2}
            y={wall.y - 2}
            width={wall.width + 4}
            height={wall.height + 4}
            fill="#0A0F1A"
          />
        ))}
      </g>

      {/* Nozzle stream during refill */}
      {nozzleStreamOpacity > 0 && (
        <rect
          x={NOZZLE_X - 3}
          y={NOZZLE_Y}
          width={6}
          height={cavityTop - NOZZLE_Y + liquidClipHeight * 0.3}
          fill={LIQUID_CYAN}
          opacity={nozzleStreamOpacity}
          rx={3}
        />
      )}
    </svg>
  );
};
