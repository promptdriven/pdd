import React, { useMemo } from 'react';
import { AbsoluteFill, useCurrentFrame, Easing, interpolate } from 'remotion';
import ModuleBlock from './ModuleBlock';
import DependencyEdge from './DependencyEdge';
import AnimatedCounter from './AnimatedCounter';
import {
  BG_COLOR,
  MODULES,
  EDGES,
  WAVES,
  TOPOLOGY_X,
  TOPOLOGY_Y,
  TOPOLOGY_W,
  TOPOLOGY_H,
  FLASH_IN_FRAMES,
  FLASH_HOLD_FRAMES,
  FLASH_SETTLE_FRAMES,
  EDGE_TRANSITION_FRAMES,
  PULSE_START_FRAME,
  PULSE_PERIOD,
  PULSE_AMPLITUDE,
} from './constants';

export const defaultWhereToStart06SpreadingGlowMigrationProps = {};

type ModuleState = 'unconverted' | 'converting' | 'converted';

// ── Helpers ─────────────────────────────────────────────────────────

/** Determine the conversion start frame for a given module id, or null if not converting. */
function getModuleConversionFrame(moduleId: number): number | null {
  for (const wave of WAVES) {
    const idx = wave.moduleIds.indexOf(moduleId);
    if (idx !== -1) {
      // Wave 0 (auth_handler) is pre-converted at frame 0
      if (wave.startFrame === 0) return 0;
      return wave.startFrame + idx * wave.staggerFrames;
    }
  }
  return null;
}

/** Get state + flash intensity for a module at a given frame. */
function getModuleVisual(
  moduleId: number,
  frame: number,
): { state: ModuleState; flashIntensity: number } {
  const convFrame = getModuleConversionFrame(moduleId);

  if (convFrame === null) {
    return { state: 'unconverted', flashIntensity: 0 };
  }

  // Module 0 is pre-converted — no flash
  if (convFrame === 0 && moduleId === 0) {
    return { state: 'converted', flashIntensity: 0 };
  }

  const elapsed = frame - convFrame;

  if (elapsed < 0) {
    return { state: 'unconverted', flashIntensity: 0 };
  }

  const flashInEnd = FLASH_IN_FRAMES;
  const flashHoldEnd = flashInEnd + FLASH_HOLD_FRAMES;
  const flashSettleEnd = flashHoldEnd + FLASH_SETTLE_FRAMES;

  if (elapsed < flashInEnd) {
    // Ramping up
    const t = interpolate(elapsed, [0, flashInEnd], [0, 1], {
      easing: Easing.out(Easing.cubic),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    });
    return { state: 'converting', flashIntensity: t };
  }

  if (elapsed < flashHoldEnd) {
    // Holding at peak
    return { state: 'converting', flashIntensity: 1 };
  }

  if (elapsed < flashSettleEnd) {
    // Settling down
    const t = interpolate(
      elapsed,
      [flashHoldEnd, flashSettleEnd],
      [1, 0],
      {
        easing: Easing.out(Easing.quad),
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      },
    );
    return { state: 'converting', flashIntensity: t };
  }

  // Fully converted
  return { state: 'converted', flashIntensity: 0 };
}

/** Determine if a module is fully converted at a given frame. */
function isFullyConverted(moduleId: number, frame: number): boolean {
  const convFrame = getModuleConversionFrame(moduleId);
  if (convFrame === null) return false;
  if (moduleId === 0 && convFrame === 0) return true;
  return frame - convFrame >= FLASH_IN_FRAMES + FLASH_HOLD_FRAMES + FLASH_SETTLE_FRAMES;
}

// ── Main Component ──────────────────────────────────────────────────

export const WhereToStart06SpreadingGlowMigration: React.FC = () => {
  const frame = useCurrentFrame();

  // Pulse offset for converted modules in hold phase
  const pulseOffset = useMemo(() => {
    if (frame < PULSE_START_FRAME) return 0;
    const t = (frame - PULSE_START_FRAME) / PULSE_PERIOD;
    return Math.sin(t * Math.PI * 2) * PULSE_AMPLITUDE;
  }, [frame]);

  // Edge brighten: both endpoints must be fully converted
  const edgeBrightenProgress = useMemo(() => {
    return EDGES.map((edge) => {
      const fromConverted = isFullyConverted(edge.from, frame);
      const toConverted = isFullyConverted(edge.to, frame);
      if (!fromConverted || !toConverted) return 0;

      // Find the later conversion frame of the two endpoints
      const fromFrame = getModuleConversionFrame(edge.from) ?? 0;
      const toFrame = getModuleConversionFrame(edge.to) ?? 0;
      const laterFrame = Math.max(fromFrame, toFrame);
      const settleEnd =
        laterFrame + FLASH_IN_FRAMES + FLASH_HOLD_FRAMES + FLASH_SETTLE_FRAMES;

      const elapsed = frame - settleEnd;
      if (elapsed < 0) return 0;

      return interpolate(elapsed, [0, EDGE_TRANSITION_FRAMES], [0, 1], {
        easing: Easing.out(Easing.quad),
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      });
    });
  }, [frame]);

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Topology container */}
      <div
        style={{
          position: 'absolute',
          left: TOPOLOGY_X,
          top: TOPOLOGY_Y,
          width: TOPOLOGY_W,
          height: TOPOLOGY_H,
        }}
      >
        {/* SVG layer for edges */}
        <svg
          width={TOPOLOGY_W}
          height={TOPOLOGY_H}
          style={{ position: 'absolute', left: 0, top: 0 }}
        >
          {EDGES.map((edge, i) => {
            const fromNode = MODULES[edge.from];
            const toNode = MODULES[edge.to];
            return (
              <DependencyEdge
                key={i}
                x1={fromNode.x}
                y1={fromNode.y}
                x2={toNode.x}
                y2={toNode.y}
                brightenProgress={edgeBrightenProgress[i]}
              />
            );
          })}
        </svg>

        {/* Module blocks */}
        {MODULES.map((mod) => {
          const { state, flashIntensity } = getModuleVisual(mod.id, frame);

          return (
            <ModuleBlock
              key={mod.id}
              x={mod.x}
              y={mod.y}
              name={mod.name}
              state={state}
              flashIntensity={flashIntensity}
              pulseOffset={
                state === 'converted' && frame >= PULSE_START_FRAME
                  ? pulseOffset
                  : 0
              }
            />
          );
        })}
      </div>

      {/* Module counter */}
      <AnimatedCounter />
    </AbsoluteFill>
  );
};

export default WhereToStart06SpreadingGlowMigration;
