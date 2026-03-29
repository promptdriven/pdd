import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  MOLD_CENTER_X,
  MOLD_CENTER_Y,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  MOLD_BASE_COLOR,
  WALL_COLOR,
  LABEL_TEXT_COLOR,
  LIQUID_COLOR,
  FLASH_COLOR,
  BASE_WALLS,
  WALL_CYCLES,
  NEW_WALL_POSITIONS,
  FLASH_FRAMES,
  WALL_SLIDE_FRAMES,
} from './constants';

/** Red flash overlay for each bug-discovery cycle */
const BugFlash: React.FC<{ cycleStartFrame: number }> = ({ cycleStartFrame }) => {
  const frame = useCurrentFrame();
  const localFrame = frame - cycleStartFrame;
  if (localFrame < 0 || localFrame >= FLASH_FRAMES) return null;

  const opacity = interpolate(localFrame, [0, FLASH_FRAMES], [0.35, 0], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.exp),
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: MOLD_CENTER_X - MOLD_WIDTH / 2 - 40,
        top: MOLD_CENTER_Y - MOLD_HEIGHT / 2 - 40,
        width: MOLD_WIDTH + 80,
        height: MOLD_HEIGHT + 80,
        backgroundColor: FLASH_COLOR,
        opacity,
        borderRadius: 12,
        pointerEvents: 'none',
      }}
    />
  );
};

/** A single new wall that slides in */
const NewWall: React.FC<{
  cycleIndex: number;
  label: string;
  side: 'left' | 'right';
  startFrame: number;
}> = ({ cycleIndex, label, side, startFrame }) => {
  const frame = useCurrentFrame();
  const pos = NEW_WALL_POSITIONS[cycleIndex];
  if (!pos) return null;

  const wallEntryStart = startFrame + FLASH_FRAMES;
  const localFrame = frame - wallEntryStart;

  if (localFrame < 0) return null;

  const slideDistance = 150;
  const slideOffset = interpolate(
    Math.min(localFrame, WALL_SLIDE_FRAMES),
    [0, WALL_SLIDE_FRAMES],
    [side === 'left' ? -slideDistance : slideDistance, 0],
    {
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.4)),
    }
  );

  const wallOpacity = interpolate(
    Math.min(localFrame, WALL_SLIDE_FRAMES),
    [0, 6],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  return (
    <g
      transform={`translate(${slideOffset}, 0)`}
      opacity={wallOpacity}
    >
      {/* Wall segment */}
      <rect
        x={pos.x - pos.wallWidth / 2}
        y={pos.y - pos.wallHeight / 2}
        width={pos.wallWidth}
        height={pos.wallHeight}
        fill={WALL_COLOR}
        rx={2}
      />
      {/* Glow */}
      <rect
        x={pos.x - pos.wallWidth / 2 - 2}
        y={pos.y - pos.wallHeight / 2 - 2}
        width={pos.wallWidth + 4}
        height={pos.wallHeight + 4}
        fill="none"
        stroke={WALL_COLOR}
        strokeWidth={2}
        opacity={0.3}
        rx={3}
      />
      {/* Label */}
      <text
        x={pos.x + pos.labelOffsetX}
        y={pos.y + pos.labelOffsetY}
        fill={LABEL_TEXT_COLOR}
        fontSize={11}
        fontFamily="'JetBrains Mono', monospace"
        textAnchor={side === 'left' ? 'end' : 'start'}
        dominantBaseline="middle"
      >
        {label}
      </text>
    </g>
  );
};

/** Liquid inside the mold that reconforms when walls are added */
const LiquidFill: React.FC = () => {
  const frame = useCurrentFrame();

  // The liquid progressively shrinks as more walls are added
  const wallCount = WALL_CYCLES.filter(
    (c) => frame >= c.startFrame + FLASH_FRAMES + WALL_SLIDE_FRAMES
  ).length;

  const shrinkFactor = interpolate(wallCount, [0, 4], [1, 0.65], {
    extrapolateRight: 'clamp',
  });

  // Subtle wobble during reconform phases
  let wobble = 0;
  for (const cycle of WALL_CYCLES) {
    const reconformStart = cycle.startFrame + FLASH_FRAMES + WALL_SLIDE_FRAMES;
    const localFrame = frame - reconformStart;
    if (localFrame >= 0 && localFrame < 20) {
      wobble += interpolate(localFrame, [0, 10, 20], [4, -2, 0], {
        extrapolateRight: 'clamp',
      });
    }
  }

  const baseLeft = MOLD_CENTER_X - (MOLD_WIDTH * 0.35 * shrinkFactor);
  const baseTop = MOLD_CENTER_Y - (MOLD_HEIGHT * 0.3 * shrinkFactor);
  const liquidW = MOLD_WIDTH * 0.7 * shrinkFactor;
  const liquidH = MOLD_HEIGHT * 0.6 * shrinkFactor;

  return (
    <rect
      x={baseLeft + wobble}
      y={baseTop}
      width={liquidW}
      height={liquidH}
      fill={LIQUID_COLOR}
      opacity={0.25}
      rx={8}
    />
  );
};

/** Glow pulse on all walls in the final hold segment (frames 216-270) */
const FinalGlow: React.FC = () => {
  const frame = useCurrentFrame();
  if (frame < 216) return null;

  const pulse = interpolate(
    (frame - 216) % 30,
    [0, 15, 30],
    [0.15, 0.35, 0.15],
    { extrapolateRight: 'clamp' }
  );

  return (
    <rect
      x={MOLD_CENTER_X - MOLD_WIDTH / 2 - 20}
      y={MOLD_CENTER_Y - MOLD_HEIGHT / 2 - 20}
      width={MOLD_WIDTH + 40}
      height={MOLD_HEIGHT + 40}
      fill="none"
      stroke={WALL_COLOR}
      strokeWidth={3}
      opacity={pulse}
      rx={10}
    />
  );
};

export const MoldCrossSection: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: 1920,
        height: 1080,
      }}
    >
      <svg width={1920} height={1080} style={{ position: 'absolute', left: 0, top: 0 }}>
        {/* Outer mold shell */}
        <rect
          x={MOLD_CENTER_X - MOLD_WIDTH / 2}
          y={MOLD_CENTER_Y - MOLD_HEIGHT / 2}
          width={MOLD_WIDTH}
          height={MOLD_HEIGHT}
          fill="none"
          stroke={MOLD_BASE_COLOR}
          strokeWidth={4}
          rx={8}
        />

        {/* Liquid fill */}
        <LiquidFill />

        {/* Base walls (pre-existing, 5 walls) */}
        {BASE_WALLS.map((wall, i) => (
          <g key={`base-${i}`}>
            <rect
              x={wall.x - wall.wallWidth / 2}
              y={wall.y - wall.wallHeight / 2}
              width={wall.wallWidth}
              height={wall.wallHeight}
              fill={WALL_COLOR}
              opacity={0.6}
              rx={2}
              transform={
                wall.rotation
                  ? `rotate(${wall.rotation} ${wall.x} ${wall.y})`
                  : undefined
              }
            />
            <text
              x={wall.x + 15}
              y={wall.y}
              fill={LABEL_TEXT_COLOR}
              fontSize={10}
              fontFamily="'JetBrains Mono', monospace"
              opacity={0.5}
              dominantBaseline="middle"
            >
              {wall.label}
            </text>
          </g>
        ))}

        {/* New walls sliding in per cycle */}
        {WALL_CYCLES.map((cycle, i) => (
          <NewWall
            key={`new-${i}`}
            cycleIndex={i}
            label={cycle.label}
            side={cycle.side}
            startFrame={cycle.startFrame}
          />
        ))}

        {/* Final glow pulse */}
        <FinalGlow />
      </svg>

      {/* Bug flash overlays */}
      {WALL_CYCLES.map((cycle, i) => (
        <BugFlash key={`flash-${i}`} cycleStartFrame={cycle.startFrame} />
      ))}
    </div>
  );
};
