import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import SyntaxLine from './SyntaxLine';
import ParticleDissolution from './ParticleDissolution';
import TypewriterCode from './TypewriterCode';
import TerminalOverlay from './TerminalOverlay';
import {
  BG_COLOR,
  GUTTER_BG,
  GUTTER_BORDER_COLOR,
  LINE_NUMBER_COLOR,
  GUTTER_WIDTH,
  CODE_TOP_PADDING,
  LINE_HEIGHT,
  CODE_FONT_SIZE,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  PATCHED_CODE_LINES,
  SELECTION_START,
  SELECTION_END,
  DISSOLUTION_START,
  EMPTY_BEAT_START,
  REGEN_START,
  REGEN_END,
  TERMINAL_START,
  SELECTION_HIGHLIGHT_COLOR,
  SELECTION_HIGHLIGHT_OPACITY,
  CURSOR_COLOR,
} from './constants';

// ── Blinking cursor ─────────────────────────────────────────────────────────

const BlinkingCursor: React.FC<{ frame: number }> = ({ frame }) => {
  // Blink every 15 frames (0.5s)
  const visible = Math.floor(frame / 15) % 2 === 0;
  return (
    <div
      style={{
        position: 'absolute',
        top: CODE_TOP_PADDING + 4,
        left: GUTTER_WIDTH + 20,
        width: 2,
        height: LINE_HEIGHT - 8,
        backgroundColor: CURSOR_COLOR,
        opacity: visible ? 1 : 0,
      }}
    />
  );
};

// ── Editor chrome wrapper ───────────────────────────────────────────────────

const EditorChrome: React.FC<{ children: React.ReactNode }> = ({ children }) => {
  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        background: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Gutter background */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: GUTTER_WIDTH,
          height: '100%',
          background: GUTTER_BG,
          borderRight: `1px solid ${GUTTER_BORDER_COLOR}`,
        }}
      />
      {children}
    </div>
  );
};

// ── Main Component ──────────────────────────────────────────────────────────

export const defaultColdOpen07CodeRegenerationProps = {};

export const ColdOpen07CodeRegeneration: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Phase logic ─────────────────────────────────────────────────────────

  const inSelection = frame >= SELECTION_START && frame < DISSOLUTION_START;
  const inDissolution = frame >= DISSOLUTION_START && frame < EMPTY_BEAT_START;
  const inEmptyBeat = frame >= EMPTY_BEAT_START && frame < REGEN_START;
  // Regen code persists once it starts (stays visible through terminal phase)
  const showRegenCode = frame >= REGEN_START;
  const showTerminal = frame >= TERMINAL_START;

  // Selection highlight opacity (easeOut quad ramp up)
  const selectionOpacity = inSelection
    ? interpolate(
        frame,
        [SELECTION_START, SELECTION_END],
        [0, SELECTION_HIGHLIGHT_OPACITY],
        { extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) },
      )
    : 0;

  const selectionBg = `${SELECTION_HIGHLIGHT_COLOR}${Math.round(selectionOpacity * 255)
    .toString(16)
    .padStart(2, '0')}`;

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      <EditorChrome>
        {/* ── Phase 1: Selection + static code ──────────────────────────── */}
        {inSelection && (
          <div style={{ position: 'absolute', top: CODE_TOP_PADDING, left: 0, width: '100%' }}>
            {PATCHED_CODE_LINES.map((line, idx) => (
              <SyntaxLine
                key={idx}
                line={line}
                lineIndex={idx}
                bgColor={selectionBg}
                lineNumber={idx + 1}
              />
            ))}
          </div>
        )}

        {/* ── Phase 2: Particle dissolution ─────────────────────────────── */}
        {inDissolution && (
          <ParticleDissolution phaseFrame={frame - DISSOLUTION_START} />
        )}

        {/* ── Phase 3: Empty beat — blinking cursor ─────────────────────── */}
        {inEmptyBeat && (
          <>
            {/* Show line numbers only (no code) */}
            <div style={{ position: 'absolute', top: CODE_TOP_PADDING, left: 0 }}>
              {Array.from({ length: 16 }, (_, i) => (
                <div
                  key={i}
                  style={{
                    position: 'absolute',
                    top: i * LINE_HEIGHT,
                    left: 0,
                    width: GUTTER_WIDTH,
                    height: LINE_HEIGHT,
                    display: 'flex',
                    alignItems: 'center',
                    justifyContent: 'flex-end',
                    paddingRight: 16,
                    fontFamily: '"JetBrains Mono", monospace',
                    fontSize: CODE_FONT_SIZE - 2,
                    color: LINE_NUMBER_COLOR,
                  }}
                >
                  {i + 1}
                </div>
              ))}
            </div>
            <BlinkingCursor frame={frame - EMPTY_BEAT_START} />
          </>
        )}

        {/* ── Phase 4: Typewriter regeneration ──────────────────────────── */}
        {showRegenCode && (
          <TypewriterCode
            phaseFrame={Math.min(frame - REGEN_START, REGEN_END - REGEN_START)}
          />
        )}

        {/* ── Phase 5: Terminal overlay ─────────────────────────────────── */}
        {showTerminal && (
          <TerminalOverlay phaseFrame={frame - TERMINAL_START} />
        )}
      </EditorChrome>
    </AbsoluteFill>
  );
};

export default ColdOpen07CodeRegeneration;
