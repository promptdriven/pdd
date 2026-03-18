// Closing05DissolveRegenerateLoop.tsx
// Section 7.5: Dissolve-Regenerate Loop — "Code Is Ephemeral"
// PDD triangle persists while code lines cycle through dissolve/regenerate loops
// 240 frames @ 30fps (~8s)

import React from 'react';
import { AbsoluteFill, Sequence, useCurrentFrame } from 'remotion';
import {
  CANVAS,
  RADIAL_GLOW,
  CODE_PATTERNS,
  CYCLES,
  TOTAL_FRAMES,
} from './constants';
import { TriangleFrame } from './TriangleFrame';
import { ParticleScatter } from './ParticleScatter';
import { CodeLines } from './CodeLines';
import { TerminalHeartbeat } from './TerminalHeartbeat';

export const defaultClosing05DissolveRegenerateLoopProps = {};

/**
 * Determines which code pattern should be statically visible at a given frame
 * (between dissolve-regenerate cycles). Returns the pattern index or -1 if
 * a cycle animation is active.
 */
function getStaticPatternIndex(frame: number): number {
  // Before first dissolve: show pattern 0
  if (frame < CYCLES[0].dissolveStart) return 0;

  for (let c = 0; c < CYCLES.length; c++) {
    const cycle = CYCLES[c];
    // During dissolve or regenerate animation: no static pattern
    if (
      frame >= cycle.dissolveStart &&
      frame < cycle.regenerateStart + cycle.regenerateDuration
    ) {
      return -1;
    }
    // After this cycle's regenerate, before next dissolve: show patternTo
    const nextDissolveStart =
      c < CYCLES.length - 1 ? CYCLES[c + 1].dissolveStart : TOTAL_FRAMES;
    if (
      frame >= cycle.regenerateStart + cycle.regenerateDuration &&
      frame < nextDissolveStart
    ) {
      return cycle.patternTo;
    }
  }

  // Fallback: last pattern
  return CYCLES[CYCLES.length - 1].patternTo;
}

export const Closing05DissolveRegenerateLoop: React.FC = () => {
  const frame = useCurrentFrame();
  const staticPatternIdx = getStaticPatternIndex(frame);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: CANVAS.backgroundColor,
        overflow: 'hidden',
      }}
    >
      {/* Radial glow background */}
      <svg
        width={CANVAS.width}
        height={CANVAS.height}
        viewBox={`0 0 ${CANVAS.width} ${CANVAS.height}`}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <defs>
          <radialGradient id="bgGlow" cx="50%" cy="48%" r="50%">
            <stop
              offset="0%"
              stopColor={RADIAL_GLOW.color}
              stopOpacity={RADIAL_GLOW.opacity}
            />
            <stop offset="100%" stopColor={CANVAS.backgroundColor} stopOpacity={0} />
          </radialGradient>
        </defs>
        <circle
          cx={RADIAL_GLOW.cx}
          cy={RADIAL_GLOW.cy}
          r={RADIAL_GLOW.radius}
          fill="url(#bgGlow)"
        />
      </svg>

      {/* Persistent triangle — completely static */}
      <TriangleFrame />

      {/* Static code lines (visible between cycles) */}
      {staticPatternIdx >= 0 && (
        <svg
          width={CANVAS.width}
          height={CANVAS.height}
          viewBox={`0 0 ${CANVAS.width} ${CANVAS.height}`}
          style={{ position: 'absolute', top: 0, left: 0 }}
        >
          {CODE_PATTERNS[staticPatternIdx].map((line, i) => (
            <rect
              key={i}
              x={960 + line.offsetX - line.width / 2}
              y={520 + line.offsetY}
              width={line.width}
              height={3}
              rx={1.5}
              fill="#94A3B8"
              opacity={0.15}
            />
          ))}
        </svg>
      )}

      {/* Cycle 1 — Slow (frames 10-70) */}
      <Sequence from={CYCLES[0].dissolveStart} durationInFrames={CYCLES[0].dissolveDuration}>
        <ParticleScatter
          lines={CODE_PATTERNS[CYCLES[0].patternFrom]}
          centerX={960}
          centerY={520}
          particlesPerLine={CYCLES[0].particlesPerLine}
          driftRadius={CYCLES[0].driftRadius}
          fadeDuration={CYCLES[0].fadeDuration}
          totalDuration={CYCLES[0].dissolveDuration}
        />
      </Sequence>
      <Sequence from={CYCLES[0].regenerateStart} durationInFrames={CYCLES[0].regenerateDuration}>
        <CodeLines
          lines={CODE_PATTERNS[CYCLES[0].patternTo]}
          centerX={960}
          centerY={520}
          stagger={CYCLES[0].stagger}
          totalDuration={CYCLES[0].regenerateDuration}
        />
      </Sequence>

      {/* Cycle 2 — Medium (frames 70-120) */}
      <Sequence from={CYCLES[1].dissolveStart} durationInFrames={CYCLES[1].dissolveDuration}>
        <ParticleScatter
          lines={CODE_PATTERNS[CYCLES[1].patternFrom]}
          centerX={960}
          centerY={520}
          particlesPerLine={CYCLES[1].particlesPerLine}
          driftRadius={CYCLES[1].driftRadius}
          fadeDuration={CYCLES[1].fadeDuration}
          totalDuration={CYCLES[1].dissolveDuration}
        />
      </Sequence>
      <Sequence from={CYCLES[1].regenerateStart} durationInFrames={CYCLES[1].regenerateDuration}>
        <CodeLines
          lines={CODE_PATTERNS[CYCLES[1].patternTo]}
          centerX={960}
          centerY={520}
          stagger={CYCLES[1].stagger}
          totalDuration={CYCLES[1].regenerateDuration}
        />
      </Sequence>

      {/* Cycle 3 — Fast (frames 120-160) */}
      <Sequence from={CYCLES[2].dissolveStart} durationInFrames={CYCLES[2].dissolveDuration}>
        <ParticleScatter
          lines={CODE_PATTERNS[CYCLES[2].patternFrom]}
          centerX={960}
          centerY={520}
          particlesPerLine={CYCLES[2].particlesPerLine}
          driftRadius={CYCLES[2].driftRadius}
          fadeDuration={CYCLES[2].fadeDuration}
          totalDuration={CYCLES[2].dissolveDuration}
        />
      </Sequence>
      <Sequence from={CYCLES[2].regenerateStart} durationInFrames={CYCLES[2].regenerateDuration}>
        <CodeLines
          lines={CODE_PATTERNS[CYCLES[2].patternTo]}
          centerX={960}
          centerY={520}
          stagger={CYCLES[2].stagger}
          totalDuration={CYCLES[2].regenerateDuration}
        />
      </Sequence>

      {/* Terminal heartbeat — bottom-right corner */}
      <TerminalHeartbeat />
    </AbsoluteFill>
  );
};

export default Closing05DissolveRegenerateLoop;
