import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Sequence,
} from 'remotion';
import {
  BG_COLOR,
  OLD_CODE_LINES,
  NEW_CODE_LINES,
  SELECTION_START,
  SELECTION_END,
  DISSOLUTION_START,
  DISSOLUTION_END,
  EMPTY_BEAT_START,
  EMPTY_BEAT_END,
  REGEN_START,
  REGEN_END,
  TERMINAL_START,
  TERMINAL_END,
} from './constants';
import { EditorChrome } from './EditorChrome';
import { StaticCodeBlock } from './StaticCodeBlock';
import { ParticleDissolution } from './ParticleDissolution';
import { BlinkingCursor } from './BlinkingCursor';
import { TypewriterCode } from './TypewriterCode';
import { TerminalOverlay } from './TerminalOverlay';

export const defaultColdOpen07CodeRegenerationProps = {};

export const ColdOpen07CodeRegeneration: React.FC = () => {
  const frame = useCurrentFrame();

  // ─── Phase determination ────────────────────────────────────────────
  const isSelectionPhase =
    frame >= SELECTION_START && frame < SELECTION_END;
  const isDissolutionPhase =
    frame >= DISSOLUTION_START && frame < DISSOLUTION_END;
  const isEmptyBeatPhase =
    frame >= EMPTY_BEAT_START && frame < EMPTY_BEAT_END;
  const isRegenPhase = frame >= REGEN_START && frame < REGEN_END;
  const isTerminalPhase = frame >= TERMINAL_START && frame <= TERMINAL_END;
  const isPostRegen = frame >= REGEN_END; // code stays visible after regen

  // The number of gutter line numbers to show varies by phase
  const gutterLineCount = (() => {
    if (frame < DISSOLUTION_END) return OLD_CODE_LINES.length;
    if (frame < REGEN_START) return 20; // empty editor still shows line nums
    return NEW_CODE_LINES.length;
  })();

  // During dissolution, fade gutter line numbers
  const gutterOpacity = isDissolutionPhase
    ? interpolate(
        frame,
        [DISSOLUTION_START, DISSOLUTION_END - 10],
        [1, 0],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
      )
    : isEmptyBeatPhase
    ? 0.3
    : 1;

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Editor chrome (gutter + line numbers) */}
      <div style={{ position: 'absolute', inset: 0, opacity: gutterOpacity }}>
        <EditorChrome lineCount={gutterLineCount}>
          <div />
        </EditorChrome>
      </div>

      {/* ── Phase 1: Selection highlight on old code (frames 0-20) ──── */}
      {isSelectionPhase && (
        <Sequence from={SELECTION_START} durationInFrames={SELECTION_END - SELECTION_START}>
          <StaticCodeBlock
            codeLines={OLD_CODE_LINES}
            showSelection={true}
            selectionProgress={interpolate(
              frame - SELECTION_START,
              [0, 8],
              [0, 1],
              { extrapolateRight: 'clamp' }
            )}
          />
        </Sequence>
      )}

      {/* Show the old code statically at frame 0 even before selection
          (visible from frame 0 requirement) — selection phase already
          handles this by rendering the code, so we only need this for
          the exact overlap at frame 0 */}

      {/* ── Phase 2: Particle dissolution (frames 20-75) ──────────── */}
      {isDissolutionPhase && (
        <ParticleDissolution
          codeLines={OLD_CODE_LINES}
          phaseFrame={frame - DISSOLUTION_START}
          phaseDuration={DISSOLUTION_END - DISSOLUTION_START}
        />
      )}

      {/* ── Phase 3: Empty beat with blinking cursor (frames 75-105) ─ */}
      {isEmptyBeatPhase && (
        <Sequence from={EMPTY_BEAT_START} durationInFrames={EMPTY_BEAT_END - EMPTY_BEAT_START}>
          <BlinkingCursor line={0} column={0} />
        </Sequence>
      )}

      {/* ── Phase 4: Clean code regeneration (frames 105-210) ──────── */}
      {(isRegenPhase || isPostRegen) && (
        <TypewriterCode
          codeLines={NEW_CODE_LINES}
          phaseFrame={
            isPostRegen && !isRegenPhase
              ? REGEN_END - REGEN_START // fully typed
              : frame - REGEN_START
          }
        />
      )}

      {/* ── Phase 5: Terminal overlay (frames 210-270) ─────────────── */}
      {isTerminalPhase && (
        <TerminalOverlay phaseFrame={frame - TERMINAL_START} />
      )}
    </AbsoluteFill>
  );
};

export default ColdOpen07CodeRegeneration;
