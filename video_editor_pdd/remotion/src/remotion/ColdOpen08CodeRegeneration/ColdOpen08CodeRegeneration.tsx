import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  spring,
  useVideoConfig,
} from 'remotion';
import CodeLine from './CodeLine';
import SelectionHighlight from './SelectionHighlight';
import TerminalOverlay from './TerminalOverlay';
import {
  BG_COLOR,
  EDITOR_PADDING_TOP,
  CODE_LINE_HEIGHT,
  PATCHED_CODE,
  REGENERATED_CODE,
  FUNCTION_SIGNATURE,
  PHASE_SELECT_START,
  PHASE_SELECT_END,
  PHASE_DELETE_START,
  PHASE_DELETE_END,
  PHASE_VOID_END,
  PHASE_REGEN_START,
  PHASE_REGEN_END,
  PHASE_TERMINAL_START,
  PHASE_TERMINAL_END,
} from './constants';

export const defaultColdOpen08CodeRegenerationProps = {};

/**
 * Code Regeneration — Delete and Rebuild
 *
 * Shows patched code being selected, deleted, then clean code flowing in.
 * 60 frames @ 30fps = 2 seconds.
 */
export const ColdOpen08CodeRegeneration: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // ============================
  // Phase 1: Selection sweep (frames 0-8)
  // 5 lines per frame, linear sweep across 40 lines
  // ============================
  const selectionProgress = interpolate(
    frame,
    [PHASE_SELECT_START, PHASE_SELECT_END],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );
  const selectedLineCount = Math.round(selectionProgress * PATCHED_CODE.length);

  // ============================
  // Phase 2: Delete (frames 8-12)
  // Code opacity fades quickly with easeIn(quad)
  // ============================
  const deleteProgress = interpolate(
    frame,
    [PHASE_DELETE_START, PHASE_DELETE_END],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  // Selection highlight fades out with deletion
  const selectionFade = frame < PHASE_DELETE_START ? 1 : deleteProgress;

  // ============================
  // Phase 3: Void (frames 12-14)
  // Just the function signature visible
  // ============================
  const isInVoid =
    frame >= PHASE_DELETE_END && frame < PHASE_VOID_END;

  // ============================
  // Phase 4: Regeneration (frames 14-44)
  // One line per frame, each line with easeOut(cubic) settle
  // ============================
  const regenLineCount =
    frame < PHASE_REGEN_START
      ? 0
      : Math.min(
          frame - PHASE_REGEN_START + 1,
          REGENERATED_CODE.length,
        );

  // ============================
  // Phase 5: Terminal overlay (frames 38-48)
  // ============================
  const terminalOpacity = interpolate(
    frame,
    [PHASE_TERMINAL_START, PHASE_TERMINAL_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Checkmark glow using spring
  const checkmarkGlow =
    frame >= PHASE_TERMINAL_END
      ? spring({
          frame: frame - PHASE_TERMINAL_END,
          fps,
          config: { stiffness: 200, damping: 15 },
        })
      : 0;

  // ============================
  // Determine which phase we're in for rendering
  // ============================
  const showPatched = frame < PHASE_DELETE_END;
  const showVoid = isInVoid;
  const showRegenerated = frame >= PHASE_REGEN_START;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Code editor area */}
      <div
        style={{
          position: 'absolute',
          top: EDITOR_PADDING_TOP,
          left: 0,
          right: 0,
          bottom: 0,
        }}
      >
        {/* === PATCHED CODE (visible during select + delete phases) === */}
        {showPatched && (
          <div style={{ position: 'relative', opacity: frame >= PHASE_DELETE_START ? deleteProgress : 1 }}>
            {/* Selection highlight overlay */}
            {frame < PHASE_DELETE_END && (
              <div style={{ opacity: selectionFade }}>
                <SelectionHighlight
                  selectedLineCount={selectedLineCount}
                  totalLines={PATCHED_CODE.length}
                />
              </div>
            )}

            {/* Patched code lines */}
            {PATCHED_CODE.map((tokens, i) => (
              <CodeLine
                key={`patched-${i}`}
                tokens={tokens}
                lineNumber={i + 1}
              />
            ))}
          </div>
        )}

        {/* === VOID PHASE (just function signature) === */}
        {showVoid && !showPatched && (
          <div style={{ position: 'relative' }}>
            {FUNCTION_SIGNATURE.map((tokens, i) => (
              <CodeLine
                key={`sig-${i}`}
                tokens={tokens}
                lineNumber={i + 1}
              />
            ))}
          </div>
        )}

        {/* === REGENERATED CODE (flows in line by line) === */}
        {showRegenerated && (
          <div style={{ position: 'relative' }}>
            {REGENERATED_CODE.map((tokens, i) => {
              const lineIndex = i;
              const lineFrame = PHASE_REGEN_START + lineIndex;
              const isVisible = lineIndex < regenLineCount;

              if (!isVisible) return null;

              // Each line has an easeOut(cubic) settle animation
              const lineLocalFrame = frame - lineFrame;
              const lineOpacity = interpolate(
                lineLocalFrame,
                [0, 4],
                [0, 1],
                {
                  extrapolateLeft: 'clamp',
                  extrapolateRight: 'clamp',
                  easing: Easing.out(Easing.cubic),
                },
              );
              const lineYOffset = interpolate(
                lineLocalFrame,
                [0, 4],
                [8, 0],
                {
                  extrapolateLeft: 'clamp',
                  extrapolateRight: 'clamp',
                  easing: Easing.out(Easing.cubic),
                },
              );

              return (
                <CodeLine
                  key={`regen-${i}`}
                  tokens={tokens}
                  lineNumber={i + 1}
                  opacity={lineOpacity}
                  yOffset={lineYOffset}
                />
              );
            })}
          </div>
        )}
      </div>

      {/* === TERMINAL OVERLAY === */}
      <TerminalOverlay opacity={terminalOpacity} checkmarkGlow={checkmarkGlow} />
    </AbsoluteFill>
  );
};

export default ColdOpen08CodeRegeneration;
