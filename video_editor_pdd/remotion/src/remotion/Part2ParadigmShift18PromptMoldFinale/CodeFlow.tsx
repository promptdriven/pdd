import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CODE_TEXT_COLOR,
  PROMPT_X,
  PROMPT_Y,
  PROMPT_HEIGHT,
  CAVITY_X,
  CAVITY_Y,
  CAVITY_WIDTH,
  CAVITY_HEIGHT,
  CODE_FLOW_START,
  CODE_FILL_DURATION,
  REGEN_INTERVAL,
  DISSOLVE_DURATION,
  REFILL_DURATION,
  CODE_GENERATIONS,
} from './constants';

/**
 * Streaming code that flows from the prompt document into the mold cavity.
 * Code regenerates every REGEN_INTERVAL frames with a dissolve/refill cycle.
 * Returns the current generation index for the parent to coordinate wall flashes.
 */

interface StreamParticle {
  x: number;
  y: number;
  delay: number; // frame offset within fill
}

function generateParticlePositions(lineCount: number): StreamParticle[] {
  const particles: StreamParticle[] = [];
  const lineHeight = 18;
  const startX = CAVITY_X + 20;
  const startY = CAVITY_Y + 16;

  for (let i = 0; i < lineCount; i++) {
    particles.push({
      x: startX,
      y: startY + i * lineHeight,
      delay: i * 2, // stagger each line by 2 frames
    });
  }
  return particles;
}

export const CodeFlow: React.FC = () => {
  const frame = useCurrentFrame();
  const localFrame = frame - CODE_FLOW_START;
  const clampedLocalFrame = Math.max(0, localFrame);

  // Determine which generation we're in and the phase within it
  const generationIndex = Math.min(
    Math.floor(clampedLocalFrame / REGEN_INTERVAL),
    CODE_GENERATIONS.length - 1
  );
  const frameInGeneration = clampedLocalFrame - generationIndex * REGEN_INTERVAL;

  // For first generation, we have a longer fill; for subsequent, dissolve→fill cycle
  const isFirstGeneration = generationIndex === 0;

  // Phase logic for non-first generations:
  //   0..DISSOLVE_DURATION: dissolve old code
  //   DISSOLVE_DURATION..DISSOLVE_DURATION+REFILL_DURATION: refill new code
  //   after that: hold

  const currentCode = CODE_GENERATIONS[generationIndex];
  const particles = useMemo(
    () => generateParticlePositions(currentCode.length),
    [currentCode.length]
  );

  if (localFrame < 0) return null;

  // Stream particles from prompt location
  const sourceX = PROMPT_X;
  const sourceY = PROMPT_Y + PROMPT_HEIGHT;

  // Compute overall opacity and per-line progress
  let overallOpacity = 1;
  let fillProgress = 1; // 0..1 how far along the fill is

  if (isFirstGeneration) {
    // First gen: fill over CODE_FILL_DURATION frames
    fillProgress = interpolate(
      frameInGeneration,
      [0, CODE_FILL_DURATION],
      [0, 1],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
    );
  } else {
    // Dissolve phase
    if (frameInGeneration < DISSOLVE_DURATION) {
      overallOpacity = interpolate(
        frameInGeneration,
        [0, DISSOLVE_DURATION],
        [1, 0],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.in(Easing.quad) }
      );
      fillProgress = 1; // old code is fully placed, just fading
    }
    // Refill phase
    else if (frameInGeneration < DISSOLVE_DURATION + REFILL_DURATION) {
      const refillFrame = frameInGeneration - DISSOLVE_DURATION;
      fillProgress = interpolate(
        refillFrame,
        [0, REFILL_DURATION],
        [0, 1],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
      );
      overallOpacity = 1;
    }
    // Hold phase
    else {
      fillProgress = 1;
      overallOpacity = 1;
    }
  }

  // Shimmer effect during dissolve
  const isDissolving = !isFirstGeneration && frameInGeneration < DISSOLVE_DURATION;
  const shimmerOffset = isDissolving
    ? Math.sin(frameInGeneration * 0.8) * 3
    : 0;

  return (
    <>
      {/* Stream particles (visual effect connecting prompt to cavity) */}
      {fillProgress < 1 && !isDissolving && (
        <StreamParticles
          sourceX={sourceX}
          sourceY={sourceY}
          targetY={CAVITY_Y}
          progress={fillProgress}
          localFrame={frameInGeneration}
        />
      )}

      {/* Code lines in cavity */}
      <div
        style={{
          position: 'absolute',
          left: CAVITY_X,
          top: CAVITY_Y,
          width: CAVITY_WIDTH,
          height: CAVITY_HEIGHT,
          overflow: 'hidden',
          opacity: overallOpacity,
        }}
      >
        {currentCode.map((line, i) => {
          const particle = particles[i];
          if (!particle) return null;

          // Each line appears based on fill progress and its delay
          const maxDelay = (currentCode.length - 1) * 2;
          const lineThreshold = maxDelay > 0 ? particle.delay / maxDelay : 0;
          const lineVisible = fillProgress >= lineThreshold;

          if (!lineVisible && !isDissolving) return null;

          // Line's individual entrance progress
          // Ensure the input range is always strictly increasing
          const lineEnd = Math.max(lineThreshold + 0.15, lineThreshold + 0.001);
          const lineProgress = interpolate(
            fillProgress,
            [lineThreshold, lineEnd],
            [0, 1],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
          );

          // Animate Y from source toward final position
          const lineY = interpolate(
            lineProgress,
            [0, 1],
            [particle.y - CAVITY_Y - 30, particle.y - CAVITY_Y],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
          );

          return (
            <div
              key={`${generationIndex}-${i}`}
              style={{
                position: 'absolute',
                left: 20,
                top: lineY + shimmerOffset * (i % 2 === 0 ? 1 : -1),
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 12,
                color: CODE_TEXT_COLOR,
                opacity: 0.6 * lineProgress,
                whiteSpace: 'pre',
                lineHeight: '18px',
              }}
            >
              {line}
            </div>
          );
        })}
      </div>
    </>
  );
};

/**
 * Small glowing particles streaming from prompt to cavity during fill.
 */
const StreamParticles: React.FC<{
  sourceX: number;
  sourceY: number;
  targetY: number;
  progress: number;
  localFrame: number;
}> = ({ sourceX, sourceY, targetY, progress, localFrame }) => {
  const particleCount = 6;
  const particles = useMemo(() => {
    return Array.from({ length: particleCount }, (_, i) => ({
      offsetX: (i - particleCount / 2) * 20 + (Math.sin(i * 2.5) * 15),
      speed: 0.6 + (i % 3) * 0.2,
      size: 3 + (i % 2) * 2,
    }));
  }, []);

  return (
    <>
      {particles.map((p, i) => {
        const t = ((localFrame * p.speed + i * 10) % 40) / 40; // 0..1 cycle
        const px = sourceX + p.offsetX + Math.sin(t * Math.PI * 2) * 8;
        const py = sourceY + t * (targetY - sourceY);
        const particleOpacity = progress < 0.95
          ? Math.sin(t * Math.PI) * 0.6
          : 0;

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: px - p.size / 2,
              top: py - p.size / 2,
              width: p.size,
              height: p.size,
              borderRadius: '50%',
              backgroundColor: CODE_TEXT_COLOR,
              opacity: particleOpacity,
              filter: 'blur(1px)',
              pointerEvents: 'none',
            }}
          />
        );
      })}
    </>
  );
};

export default CodeFlow;
