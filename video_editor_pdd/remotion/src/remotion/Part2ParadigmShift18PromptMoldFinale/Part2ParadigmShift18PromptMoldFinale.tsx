import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from 'remotion';
import {
  BG_COLOR,
  TOTAL_FRAMES,
  FADE_OUT_START,
  FADE_OUT_DURATION,
  CODE_FLOW_START,
  REGEN_INTERVAL,
  DISSOLVE_DURATION,
  WALL_FLASH_DURATION,
  PROMPT_COLOR,
  PROMPT_X,
  PROMPT_Y,
  PROMPT_HEIGHT,
  CAVITY_X,
  CAVITY_Y,
  CAVITY_WIDTH,
  CODE_GENERATIONS,
} from './constants';
import { PulsingDocument } from './PulsingDocument';
import { TestWalls } from './TestWalls';
import { CodeFlow } from './CodeFlow';

export const defaultPart2ParadigmShift18PromptMoldFinaleProps = {};

/**
 * Section 2.18: "The Prompt Is Your Mold" — Finale
 *
 * A glowing PROMPT document emits code lines that flow into a mold cavity
 * constrained by test-assertion walls. Code regenerates but the walls hold firm.
 * The prompt is the mold. The code is the plastic. The tests are the walls.
 *
 * Duration: 360 frames @ 30fps (~12s)
 */
export const Part2ParadigmShift18PromptMoldFinale: React.FC = () => {
  const frame = useCurrentFrame();

  // ─── Fade-out to black (frames 300-360) ───────────────
  const fadeOutOpacity = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_START + FADE_OUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  // ─── Wall flash state ─────────────────────────────────
  // Flash the walls when a regeneration cycle starts (every REGEN_INTERVAL after CODE_FLOW_START)
  const codeLocalFrame = frame - CODE_FLOW_START;
  const generationIndex =
    codeLocalFrame >= 0
      ? Math.min(
          Math.floor(codeLocalFrame / REGEN_INTERVAL),
          CODE_GENERATIONS.length - 1
        )
      : 0;
  const frameInGeneration =
    codeLocalFrame >= 0 ? codeLocalFrame - generationIndex * REGEN_INTERVAL : -1;

  // Flash at the end of dissolve phase for non-first generations
  const isFlashing =
    generationIndex > 0 &&
    frameInGeneration >= DISSOLVE_DURATION &&
    frameInGeneration < DISSOLVE_DURATION + WALL_FLASH_DURATION;

  const flashIntensity = isFlashing
    ? interpolate(
        frameInGeneration,
        [DISSOLVE_DURATION, DISSOLVE_DURATION + WALL_FLASH_DURATION],
        [1, 0],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.quad),
        }
      )
    : 0;

  // ─── Connection line: prompt → cavity ─────────────────
  const connectionLineOpacity =
    frame >= CODE_FLOW_START
      ? interpolate(
          frame,
          [CODE_FLOW_START, CODE_FLOW_START + 20],
          [0, 0.25],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        )
      : 0;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      <div style={{ opacity: fadeOutOpacity, width: '100%', height: '100%' }}>
        {/* Subtle radial gradient behind the cavity for depth */}
        <div
          style={{
            position: 'absolute',
            left: CAVITY_X - 100,
            top: CAVITY_Y - 100,
            width: CAVITY_WIDTH + 200,
            height: 600,
            background: `radial-gradient(ellipse at center, ${PROMPT_COLOR}08 0%, transparent 70%)`,
            pointerEvents: 'none',
          }}
        />

        {/* Connection line from prompt to cavity */}
        <div
          style={{
            position: 'absolute',
            left: PROMPT_X - 1,
            top: PROMPT_Y + PROMPT_HEIGHT,
            width: 2,
            height: CAVITY_Y - (PROMPT_Y + PROMPT_HEIGHT),
            background: `linear-gradient(to bottom, ${PROMPT_COLOR}66, ${PROMPT_COLOR}00)`,
            opacity: connectionLineOpacity,
            pointerEvents: 'none',
          }}
        />

        {/* Prompt document (visible from frame 0) */}
        <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
          <PulsingDocument />
        </Sequence>

        {/* Test walls (draw from frame 45) */}
        <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
          <TestWalls
            wallFlash={{ active: isFlashing, intensity: flashIntensity }}
          />
        </Sequence>

        {/* Code flow with regeneration (from frame 90) */}
        <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
          <CodeFlow />
        </Sequence>

        {/* Generation counter (subtle) */}
        {codeLocalFrame >= 0 && (
          <div
            style={{
              position: 'absolute',
              right: 80,
              bottom: 60,
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 13,
              color: '#E2E8F0',
              opacity: 0.3,
              letterSpacing: 1,
            }}
          >
            gen {generationIndex + 1}/{CODE_GENERATIONS.length}
          </div>
        )}

        {/* Thesis text (appears during hold phase) */}
        <ThesisText frame={frame} />
      </div>
    </AbsoluteFill>
  );
};

/**
 * Thesis text that fades in during the hold phase.
 */
const ThesisText: React.FC<{ frame: number }> = ({ frame }) => {
  const textStart = 240; // frames — during final hold
  const textFadeDuration = 30;

  if (frame < textStart) return null;

  const opacity = interpolate(
    frame,
    [textStart, textStart + textFadeDuration],
    [0, 0.85],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  return (
    <div
      style={{
        position: 'absolute',
        bottom: 120,
        left: 0,
        right: 0,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        gap: 8,
        opacity,
      }}
    >
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 22,
          fontWeight: 600,
          color: '#FFFFFF',
          letterSpacing: 1.5,
          textAlign: 'center',
        }}
      >
        THE PROMPT IS YOUR MOLD
      </div>
      <div
        style={{
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: 14,
          color: '#E2E8F0',
          opacity: 0.62,
          letterSpacing: 0.5,
        }}
      >
        the code is just plastic
      </div>
    </div>
  );
};

export default Part2ParadigmShift18PromptMoldFinale;
