import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
} from 'remotion';

import {
  BG_COLOR,
  GUTTER_BG,
  GUTTER_TEXT_COLOR,
  SELECTION_COLOR,
  SELECTION_OPACITY,
  TOKEN_COLOR_MAP,
  PATCHED_CODE,
  REGENERATED_CODE,
  FUNCTION_SIGNATURE,
  CODE_LINE_HEIGHT,
  CODE_FONT_SIZE,
  EDITOR_PADDING_TOP,
  GUTTER_WIDTH,
  TERMINAL_BG,
  TERMINAL_BG_OPACITY,
  TERMINAL_TEXT_COLOR,
  TERMINAL_FONT_SIZE,
  TERMINAL_WIDTH,
  TERMINAL_HEIGHT,
  TERMINAL_RIGHT,
  TERMINAL_BOTTOM,
  TERMINAL_BORDER_RADIUS,
  PHASE_SELECT_START,
  PHASE_SELECT_END,
  PHASE_DELETE_START,
  PHASE_DELETE_END,
  PHASE_VOID_END,
  PHASE_REGEN_START,
  PHASE_TERMINAL_START,
  PHASE_TERMINAL_END,
} from './constants';

import { SelectionHighlight } from './SelectionHighlight';
import { CodeLines } from './CodeLines';
import { TerminalOverlay } from './TerminalOverlay';

export const defaultColdOpen08CodeRegenerationProps = {};

/**
 * Section 0.8 – Code Regeneration: Delete and Rebuild
 *
 * 60 frames @ 30fps. Shows a patched function being selected, deleted,
 * then regenerated with clean code. Terminal overlay confirms the command.
 */
export const ColdOpen08CodeRegeneration: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // ── Phase calculations ──────────────────────────────

  // Patched code visibility: visible frames 0–12, fades out during delete
  const patchedOpacity = interpolate(
    frame,
    [PHASE_DELETE_START, PHASE_DELETE_END],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  // Show patched code only before deletion completes
  const showPatched = frame < PHASE_DELETE_END;

  // After delete, show just the signature in the void beat
  const showVoidSignature = frame >= PHASE_DELETE_END && frame < PHASE_REGEN_START;

  // Show regenerated code flowing in
  const showRegenerated = frame >= PHASE_REGEN_START;

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* ── Editor Chrome: tab bar ── */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          right: 0,
          height: 32,
          backgroundColor: '#181825',
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 12,
        }}
      >
        <div
          style={{
            padding: '4px 16px',
            backgroundColor: BG_COLOR,
            color: '#CDD6F4',
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: 12,
            borderTopLeftRadius: 4,
            borderTopRightRadius: 4,
          }}
        >
          process_order.py
        </div>
      </div>

      {/* ── Code area (below tab bar) ── */}
      <div
        style={{
          position: 'absolute',
          top: 32,
          left: 0,
          right: 0,
          bottom: 0,
        }}
      >
        {/* ── Phase 1: Patched code (frame 0–12) ── */}
        {showPatched && (
          <CodeLines
            lines={PATCHED_CODE}
            startLineNumber={1}
            lineHeight={CODE_LINE_HEIGHT}
            fontSize={CODE_FONT_SIZE}
            gutterWidth={GUTTER_WIDTH}
            paddingTop={EDITOR_PADDING_TOP}
            gutterBg={GUTTER_BG}
            gutterTextColor={GUTTER_TEXT_COLOR}
            tokenColorMap={TOKEN_COLOR_MAP}
            opacity={patchedOpacity}
          />
        )}

        {/* ── Selection sweep overlay (frame 0–8) ── */}
        {frame < PHASE_SELECT_END && (
          <SelectionHighlight
            totalLines={PATCHED_CODE.length}
            lineHeight={CODE_LINE_HEIGHT}
            gutterWidth={GUTTER_WIDTH}
            paddingTop={EDITOR_PADDING_TOP}
            selectionColor={SELECTION_COLOR}
            selectionOpacity={SELECTION_OPACITY}
            sweepStartFrame={PHASE_SELECT_START}
            sweepEndFrame={PHASE_SELECT_END}
          />
        )}

        {/* ── Phase 3: Void — just the function signature ── */}
        {showVoidSignature && (
          <CodeLines
            lines={[FUNCTION_SIGNATURE.map((t) => ({ ...t }))]}
            startLineNumber={1}
            lineHeight={CODE_LINE_HEIGHT}
            fontSize={CODE_FONT_SIZE}
            gutterWidth={GUTTER_WIDTH}
            paddingTop={EDITOR_PADDING_TOP}
            gutterBg={GUTTER_BG}
            gutterTextColor={GUTTER_TEXT_COLOR}
            tokenColorMap={TOKEN_COLOR_MAP}
          />
        )}

        {/* ── Phase 4: Regenerated code flows in (frame 14–44) ── */}
        {showRegenerated && (
          <CodeLines
            lines={REGENERATED_CODE}
            startLineNumber={1}
            lineHeight={CODE_LINE_HEIGHT}
            fontSize={CODE_FONT_SIZE}
            gutterWidth={GUTTER_WIDTH}
            paddingTop={EDITOR_PADDING_TOP}
            gutterBg={GUTTER_BG}
            gutterTextColor={GUTTER_TEXT_COLOR}
            tokenColorMap={TOKEN_COLOR_MAP}
            flowInStartFrame={PHASE_REGEN_START}
          />
        )}

        {/* ── Blinking cursor ── */}
        <BlinkingCursor
          frame={frame}
          lineHeight={CODE_LINE_HEIGHT}
          paddingTop={EDITOR_PADDING_TOP}
          gutterWidth={GUTTER_WIDTH}
          fontSize={CODE_FONT_SIZE}
        />
      </div>

      {/* ── Phase 5: Terminal overlay (frame 38–60) ── */}
      <TerminalOverlay
        fadeInStartFrame={PHASE_TERMINAL_START}
        fadeInDuration={PHASE_TERMINAL_END - PHASE_TERMINAL_START}
        command="pdd generate process_order"
        bgColor={TERMINAL_BG}
        bgOpacity={TERMINAL_BG_OPACITY}
        textColor={TERMINAL_TEXT_COLOR}
        fontSize={TERMINAL_FONT_SIZE}
        width={TERMINAL_WIDTH}
        height={TERMINAL_HEIGHT}
        right={TERMINAL_RIGHT}
        bottom={TERMINAL_BOTTOM}
        borderRadius={TERMINAL_BORDER_RADIUS}
        fps={fps}
      />
    </AbsoluteFill>
  );
};

// ── Blinking cursor helper ──────────────────────────────

interface BlinkingCursorProps {
  frame: number;
  lineHeight: number;
  paddingTop: number;
  gutterWidth: number;
  fontSize: number;
}

const BlinkingCursor: React.FC<BlinkingCursorProps> = ({
  frame,
  lineHeight,
  paddingTop,
  gutterWidth,
  fontSize,
}) => {
  // Determine cursor position based on current phase
  let cursorLine: number;
  let cursorVisible = true;

  if (frame < 12) {
    // During select/delete: cursor at end of patched code
    cursorLine = PATCHED_CODE.length - 1;
    // Hide during selection sweep
    if (frame < 8) cursorVisible = false;
  } else if (frame < 14) {
    // Void: cursor on line 2 (empty body)
    cursorLine = 1;
  } else {
    // Regeneration: cursor at the latest visible line
    const linesShown = Math.min(frame - 14 + 1, REGENERATED_CODE.length);
    cursorLine = linesShown - 1;
  }

  // Blink every ~16 frames (about 0.5s at 30fps)
  const blinkOn = Math.floor(frame / 16) % 2 === 0;
  if (!cursorVisible || !blinkOn) return null;

  return (
    <div
      style={{
        position: 'absolute',
        top: paddingTop + cursorLine * lineHeight + 2,
        left: gutterWidth + 8,
        width: 2,
        height: fontSize + 2,
        backgroundColor: '#CDD6F4',
      }}
    />
  );
};

export default ColdOpen08CodeRegeneration;
