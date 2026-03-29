import React, { useMemo } from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame } from 'remotion';
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  MOLD_CENTER_X,
  NOZZLE_TOP,
  NOZZLE_BOTTOM,
  CAVITY_TOP,
  CAVITY_BOTTOM,
  EXIT_TOP,
  EXIT_BOTTOM,
  MOLD_LEFT,
  MOLD_RIGHT,
  WALL_THICKNESS,
  NOZZLE_NECK_WIDTH,
  EXIT_NECK_WIDTH,
  NOZZLE_COLOR,
  CAVITY_COLOR,
  WALL_COLOR,
  EXIT_COLOR,
  PARTICLE_COUNT,
  FLOW_CYCLE_FRAMES,
} from './constants';

// Pseudo-random seeded generator for deterministic particles
function seededRandom(seed: number): number {
  const x = Math.sin(seed * 12.9898 + seed * 78.233) * 43758.5453;
  return x - Math.floor(x);
}

interface Particle {
  id: number;
  offset: number; // 0..1 phase offset for staggering
  xJitter: number; // horizontal randomness
  size: number;
}

// The vertical flow path is: NOZZLE_TOP -> NOZZLE_BOTTOM -> CAVITY region -> EXIT_TOP -> EXIT_BOTTOM
// Normalized: 0 = top of nozzle, 1 = bottom of exit
const TOTAL_PATH_LENGTH = EXIT_BOTTOM - NOZZLE_TOP;

function getYFromProgress(progress: number): number {
  return NOZZLE_TOP + progress * TOTAL_PATH_LENGTH;
}

function getColorFromProgress(progress: number): string {
  const nozzleEnd = (NOZZLE_BOTTOM - NOZZLE_TOP) / TOTAL_PATH_LENGTH;
  const cavityEnd = (CAVITY_BOTTOM - NOZZLE_TOP) / TOTAL_PATH_LENGTH;
  const exitStart = (EXIT_TOP - NOZZLE_TOP) / TOTAL_PATH_LENGTH;

  if (progress < nozzleEnd) return NOZZLE_COLOR;
  if (progress < (nozzleEnd + cavityEnd) / 2) {
    // Transition from amber to teal
    const t = interpolate(progress, [nozzleEnd, (nozzleEnd + cavityEnd) / 2], [0, 1], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    });
    return t < 0.5 ? NOZZLE_COLOR : CAVITY_COLOR;
  }
  if (progress < exitStart) return CAVITY_COLOR;
  if (progress < (exitStart + 1) / 2) return WALL_COLOR;
  return EXIT_COLOR;
}

function getXSpreadFromProgress(progress: number): number {
  const nozzleEnd = (NOZZLE_BOTTOM - NOZZLE_TOP) / TOTAL_PATH_LENGTH;
  const cavityStart = (CAVITY_TOP - NOZZLE_TOP) / TOTAL_PATH_LENGTH;
  const exitStart = (EXIT_TOP - NOZZLE_TOP) / TOTAL_PATH_LENGTH;

  if (progress < nozzleEnd) {
    return NOZZLE_NECK_WIDTH / 2 - 10;
  }
  if (progress < cavityStart + 0.05) {
    // Expand from nozzle width to cavity width
    const t = interpolate(progress, [nozzleEnd, cavityStart + 0.05], [0, 1], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    });
    const nozzleHalf = NOZZLE_NECK_WIDTH / 2 - 10;
    const cavityHalf = (MOLD_RIGHT - MOLD_LEFT) / 2 - WALL_THICKNESS - 10;
    return nozzleHalf + t * (cavityHalf - nozzleHalf);
  }
  if (progress < exitStart) {
    return (MOLD_RIGHT - MOLD_LEFT) / 2 - WALL_THICKNESS - 10;
  }
  // Narrow to exit
  const t = interpolate(progress, [exitStart, 1], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });
  const cavityHalf = (MOLD_RIGHT - MOLD_LEFT) / 2 - WALL_THICKNESS - 10;
  const exitHalf = EXIT_NECK_WIDTH / 2 - 10;
  return cavityHalf + t * (exitHalf - cavityHalf);
}

// Wall spark component
const WallSpark: React.FC<{ x: number; y: number; progress: number }> = ({
  x,
  y,
  progress,
}) => {
  const sparkOpacity = interpolate(progress, [0, 0.3, 1], [0, 1, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });
  const sparkSize = interpolate(progress, [0, 0.2, 1], [2, 6, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <circle cx={x} cy={y} r={sparkSize} fill={WALL_COLOR} opacity={sparkOpacity} />
  );
};

export const ParticleFlow: React.FC = () => {
  const frame = useCurrentFrame();

  // Particles begin at frame 30 of the parent (but this component starts from its own Sequence)
  const localFrame = frame;

  const particles = useMemo<Particle[]>(() => {
    return Array.from({ length: PARTICLE_COUNT }, (_, i) => ({
      id: i,
      offset: i / PARTICLE_COUNT,
      xJitter: seededRandom(i * 7 + 3) * 2 - 1, // -1 to 1
      size: 3 + seededRandom(i * 11 + 5) * 3,
    }));
  }, []);

  // Generate wall sparks
  const sparks = useMemo(() => {
    return Array.from({ length: 8 }, (_, i) => ({
      id: i,
      seed: seededRandom(i * 17 + 42),
      side: i % 2 === 0 ? -1 : 1,
      yOffset: seededRandom(i * 23 + 7) * 0.4 - 0.2,
    }));
  }, []);

  const exitRegionStart = (EXIT_TOP - NOZZLE_TOP) / TOTAL_PATH_LENGTH;
  const wallRegionY = CAVITY_BOTTOM;

  return (
    <AbsoluteFill>
      <svg
        width={CANVAS_WIDTH}
        height={CANVAS_HEIGHT}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <defs>
          <filter id="particleGlow" x="-100%" y="-100%" width="300%" height="300%">
            <feGaussianBlur stdDeviation="3" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Particles */}
        {particles.map((p) => {
          // Each particle cycles through the path
          const cycleProgress =
            ((localFrame / FLOW_CYCLE_FRAMES + p.offset) % 1);

          // Limit how far particles can go based on flow entry progress
          // During early frames, particles only reach partway through the mold
          const maxProgress = interpolate(
            localFrame,
            [0, 30, 60, 90],
            [
              (NOZZLE_BOTTOM - NOZZLE_TOP) / TOTAL_PATH_LENGTH,
              (CAVITY_BOTTOM - NOZZLE_TOP) / TOTAL_PATH_LENGTH * 0.5,
              exitRegionStart,
              1,
            ],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
          );

          const progress = cycleProgress * maxProgress;
          const y = getYFromProgress(progress);
          const spread = getXSpreadFromProgress(progress);
          const x = MOLD_CENTER_X + p.xJitter * spread;
          const color = getColorFromProgress(progress);

          // Guard: ensure inputRange is strictly increasing even when maxProgress is small
          const fadeInEnd = Math.min(0.02, maxProgress * 0.2);
          const fadeOutStart = Math.max(fadeInEnd + 0.001, maxProgress - 0.02);
          const fadeOutEnd = Math.max(fadeOutStart + 0.001, maxProgress);

          const particleOpacity = interpolate(
            progress,
            [0, fadeInEnd, fadeOutStart, fadeOutEnd],
            [0, 0.9, 0.9, 0],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
          );

          return (
            <circle
              key={p.id}
              cx={x}
              cy={y}
              r={p.size}
              fill={color}
              opacity={particleOpacity}
              filter="url(#particleGlow)"
            />
          );
        })}

        {/* Wall sparks: appear when flow reaches the wall region */}
        {localFrame >= 60 &&
          sparks.map((spark) => {
            const sparkCycle = (localFrame - 60 + spark.seed * 30) % 20;
            const sparkProgress = sparkCycle / 20;
            const sparkY = wallRegionY + spark.yOffset * 80;
            const sparkX =
              spark.side > 0
                ? MOLD_RIGHT - WALL_THICKNESS + 5
                : MOLD_LEFT + WALL_THICKNESS - 5;

            return (
              <WallSpark
                key={`spark-${spark.id}`}
                x={sparkX}
                y={sparkY}
                progress={sparkProgress}
              />
            );
          })}

        {/* Central flow stream (visible after exit opens) */}
        {localFrame >= 90 && (
          <line
            x1={MOLD_CENTER_X}
            y1={EXIT_TOP + 10}
            x2={MOLD_CENTER_X}
            y2={EXIT_BOTTOM + 20}
            stroke={EXIT_COLOR}
            strokeWidth={3}
            opacity={interpolate(localFrame, [90, 120], [0, 0.6], {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
            })}
            strokeLinecap="round"
          />
        )}
      </svg>
    </AbsoluteFill>
  );
};
