import React from 'react';
import { AbsoluteFill, Sequence, useCurrentFrame } from 'remotion';
import {
  BG_COLOR,
  RADIAL_GLOW_COLOR,
  RADIAL_GLOW_OPACITY,
  CENTER_X,
  CENTER_Y,
  CODE_PATTERN_1,
  CODE_PATTERN_4,
  CYCLES,
} from './constants';
import { Triangle } from './Triangle';
import { ParticleScatter } from './ParticleScatter';
import { CodeLines, StaticCodeLines } from './CodeLines';
import { TerminalHeartbeat } from './TerminalHeartbeat';

export const defaultClosing05DissolveRegenerateLoopProps = {};

export const Closing05DissolveRegenerateLoop: React.FC = () => {
  const frame = useCurrentFrame();

  // Determine if we should show static initial code (frames 0-10)
  const showInitialCode = frame < CYCLES[0].startFrame;

  // Determine if we're in the final hold (after all cycles complete)
  const lastCycle = CYCLES[CYCLES.length - 1];
  const allCyclesDone =
    frame >=
    lastCycle.startFrame + lastCycle.dissolveFrames + lastCycle.regenerateFrames;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Radial glow background */}
      <div
        style={{
          position: 'absolute',
          width: 1200,
          height: 1200,
          left: CENTER_X - 600,
          top: CENTER_Y - 600,
          borderRadius: '50%',
          background: `radial-gradient(circle, ${RADIAL_GLOW_COLOR} 0%, transparent 70%)`,
          opacity: RADIAL_GLOW_OPACITY,
          pointerEvents: 'none',
        }}
      />

      {/* Persistent triangle — completely static */}
      <Triangle />

      {/* Initial code lines (static, before first dissolve) */}
      {showInitialCode && <StaticCodeLines lines={CODE_PATTERN_1} />}

      {/* Cycle 1 — slow (frames 10-70) */}
      <Sequence from={CYCLES[0].startFrame} durationInFrames={CYCLES[0].dissolveFrames}>
        <ParticleScatter
          lines={CYCLES[0].sourcePattern}
          particlesPerLine={CYCLES[0].particlesPerLine}
          driftRadius={CYCLES[0].driftRadius}
          fadeDuration={CYCLES[0].fadeDuration}
          totalFrames={CYCLES[0].dissolveFrames}
        />
      </Sequence>
      <Sequence
        from={CYCLES[0].startFrame + CYCLES[0].dissolveFrames}
        durationInFrames={CYCLES[0].regenerateFrames}
      >
        <CodeLines
          lines={CYCLES[0].targetPattern}
          staggerFrames={CYCLES[0].staggerFrames}
          totalFrames={CYCLES[0].regenerateFrames}
        />
      </Sequence>

      {/* Cycle 2 — medium (frames 70-120) */}
      <Sequence from={CYCLES[1].startFrame} durationInFrames={CYCLES[1].dissolveFrames}>
        <ParticleScatter
          lines={CYCLES[1].sourcePattern}
          particlesPerLine={CYCLES[1].particlesPerLine}
          driftRadius={CYCLES[1].driftRadius}
          fadeDuration={CYCLES[1].fadeDuration}
          totalFrames={CYCLES[1].dissolveFrames}
        />
      </Sequence>
      <Sequence
        from={CYCLES[1].startFrame + CYCLES[1].dissolveFrames}
        durationInFrames={CYCLES[1].regenerateFrames}
      >
        <CodeLines
          lines={CYCLES[1].targetPattern}
          staggerFrames={CYCLES[1].staggerFrames}
          totalFrames={CYCLES[1].regenerateFrames}
        />
      </Sequence>

      {/* Cycle 3 — fast (frames 120-160) */}
      <Sequence from={CYCLES[2].startFrame} durationInFrames={CYCLES[2].dissolveFrames}>
        <ParticleScatter
          lines={CYCLES[2].sourcePattern}
          particlesPerLine={CYCLES[2].particlesPerLine}
          driftRadius={CYCLES[2].driftRadius}
          fadeDuration={CYCLES[2].fadeDuration}
          totalFrames={CYCLES[2].dissolveFrames}
        />
      </Sequence>
      <Sequence
        from={CYCLES[2].startFrame + CYCLES[2].dissolveFrames}
        durationInFrames={CYCLES[2].regenerateFrames}
      >
        <CodeLines
          lines={CYCLES[2].targetPattern}
          staggerFrames={CYCLES[2].staggerFrames}
          totalFrames={CYCLES[2].regenerateFrames}
        />
      </Sequence>

      {/* Final hold — show last code pattern statically (frames 160-240) */}
      {allCyclesDone && <StaticCodeLines lines={CODE_PATTERN_4} />}

      {/* Terminal heartbeat — bottom-right corner */}
      <TerminalHeartbeat />
    </AbsoluteFill>
  );
};

export default Closing05DissolveRegenerateLoop;
