import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import {
  WIDTH,
  HEIGHT,
  BG,
  LINE_NUMBER_COLOR,
  SELECTION_COLOR,
  TAB_TEXT_COLOR,
  STATUS_TEXT_COLOR,
  TERMINAL_GREEN,
  TOKEN_COLORS,
  EDITOR_LEFT,
  TAB_BAR_HEIGHT,
  STATUS_BAR_HEIGHT,
  LINE_HEIGHT,
  CODE_FONT_SIZE,
  LINE_NUM_FONT_SIZE,
  TAB_FONT_SIZE,
  STATUS_FONT_SIZE,
  TERMINAL_FONT_SIZE,
  SELECTION_SWEEP_DURATION,
  BLOCK_REVEAL_DURATION,
  TERMINAL_FADE_DURATION,
  PARTICLE_FADE_DURATION,
  OLD_CODE,
  NEW_CODE,
  CodeLine,
} from './constants';
import ParticleDissolve from './ParticleDissolve';

// ── Shared styles ───────────────────────────────────
const MONO_FONT = 'JetBrains Mono, Fira Code, Consolas, monospace';
const SANS_FONT = 'Inter, system-ui, sans-serif';

export const defaultColdOpen05CodeBlinkProps = {};

// ── Timeline constants (frames) ─────────────────────
const T_SELECTION_START = 30;
const T_DISSOLVE_START = 60;
const T_VOID_END = 105;
const T_BLOCK1 = 105;
const T_BLOCK2 = 120;
const T_BLOCK3 = 135;
const T_TERMINAL = 150;

// ── Sub-components ──────────────────────────────────

/** Renders a single code line with syntax coloring */
const SyntaxLine: React.FC<{
  line: CodeLine;
  lineNumber: number;
  yOffset: number;
  opacity?: number;
}> = ({ line, lineNumber, yOffset, opacity = 1 }) => (
  <div
    style={{
      position: 'absolute',
      top: yOffset,
      left: 0,
      width: WIDTH,
      height: LINE_HEIGHT,
      display: 'flex',
      alignItems: 'center',
      opacity,
    }}
  >
    {/* Line number */}
    <span
      style={{
        position: 'absolute',
        right: WIDTH - EDITOR_LEFT + 20,
        width: EDITOR_LEFT - 30,
        textAlign: 'right',
        fontFamily: MONO_FONT,
        fontSize: LINE_NUM_FONT_SIZE,
        color: LINE_NUMBER_COLOR,
        opacity: 0.4,
        userSelect: 'none',
        lineHeight: `${LINE_HEIGHT}px`,
      }}
    >
      {lineNumber}
    </span>
    {/* Code tokens */}
    <span
      style={{
        position: 'absolute',
        left: EDITOR_LEFT,
        fontFamily: MONO_FONT,
        fontSize: CODE_FONT_SIZE,
        whiteSpace: 'pre',
        lineHeight: `${LINE_HEIGHT}px`,
      }}
    >
      {line.tokens.map((token, i) => (
        <span key={i} style={{ color: TOKEN_COLORS[token.type] }}>
          {token.text}
        </span>
      ))}
    </span>
  </div>
);

/** Line numbers only (for empty editor phase) */
const EmptyLineNumbers: React.FC<{ count: number }> = ({ count }) => (
  <>
    {Array.from({ length: count }, (_, i) => (
      <span
        key={i}
        style={{
          position: 'absolute',
          top: TAB_BAR_HEIGHT + i * LINE_HEIGHT,
          right: WIDTH - EDITOR_LEFT + 20,
          width: EDITOR_LEFT - 30,
          textAlign: 'right',
          fontFamily: MONO_FONT,
          fontSize: LINE_NUM_FONT_SIZE,
          color: LINE_NUMBER_COLOR,
          opacity: 0.4,
          lineHeight: `${LINE_HEIGHT}px`,
        }}
      >
        {i + 1}
      </span>
    ))}
  </>
);

/** Blinking cursor — uses absolute frame for consistent blink rate */
const Cursor: React.FC<{ x: number; y: number; absoluteFrame: number }> = ({
  x,
  y,
  absoluteFrame,
}) => {
  const visible = Math.floor(absoluteFrame / 15) % 2 === 0;
  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width: 2,
        height: LINE_HEIGHT - 4,
        backgroundColor: '#C9D1D9',
        opacity: visible ? 0.8 : 0,
      }}
    />
  );
};

/** Selection highlight overlay — sweeps top to bottom */
const SelectionHighlight: React.FC = () => {
  const frame = useCurrentFrame(); // relative to Sequence from={T_SELECTION_START}

  const progress = interpolate(frame, [0, SELECTION_SWEEP_DURATION], [0, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const totalHeight = OLD_CODE.length * LINE_HEIGHT;
  const revealedHeight = progress * totalHeight;

  return (
    <div
      style={{
        position: 'absolute',
        left: EDITOR_LEFT - 10,
        top: TAB_BAR_HEIGHT,
        width: WIDTH - EDITOR_LEFT - 80,
        height: revealedHeight,
        backgroundColor: SELECTION_COLOR,
        opacity: 0.2,
        borderRadius: 2,
      }}
    />
  );
};

/** IDE Chrome: tab bar and status bar */
const IDEChrome: React.FC<{ absoluteFrame: number }> = ({ absoluteFrame }) => {
  const statusText =
    absoluteFrame >= T_BLOCK1
      ? `Ln ${NEW_CODE.length}, Col 1`
      : 'Ln 1, Col 1';

  return (
    <>
      {/* Tab bar */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: WIDTH,
          height: TAB_BAR_HEIGHT,
          backgroundColor: '#161B22',
          borderBottom: '1px solid #30363D',
          display: 'flex',
          alignItems: 'flex-end',
        }}
      >
        <div
          style={{
            display: 'flex',
            alignItems: 'center',
            gap: 6,
            padding: '8px 16px',
            backgroundColor: BG,
            borderTop: '2px solid #1F6FEB',
            borderRight: '1px solid #30363D',
            marginLeft: 10,
            borderTopLeftRadius: 4,
            borderTopRightRadius: 4,
          }}
        >
          <span style={{ fontSize: 14, color: '#3572A5' }}>&#9679;</span>
          <span
            style={{
              fontFamily: SANS_FONT,
              fontSize: TAB_FONT_SIZE,
              color: TAB_TEXT_COLOR,
              opacity: 0.7,
            }}
          >
            user_parser.py
          </span>
        </div>
      </div>

      {/* Status bar */}
      <div
        style={{
          position: 'absolute',
          bottom: 0,
          left: 0,
          width: WIDTH,
          height: STATUS_BAR_HEIGHT,
          backgroundColor: '#161B22',
          borderTop: '1px solid #30363D',
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 20,
        }}
      >
        <span
          style={{
            fontFamily: SANS_FONT,
            fontSize: STATUS_FONT_SIZE,
            color: STATUS_TEXT_COLOR,
            opacity: 0.3,
          }}
        >
          {statusText}
        </span>
      </div>
    </>
  );
};

/** Terminal snippet — fades in using Sequence-relative frame */
const TerminalSnippet: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, TERMINAL_FADE_DURATION], [0, 0.4], {
    easing: Easing.out(Easing.quad),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <div
      style={{
        position: 'absolute',
        right: 170,
        bottom: STATUS_BAR_HEIGHT + 16,
        display: 'flex',
        alignItems: 'center',
        gap: 4,
        opacity,
        backgroundColor: 'rgba(22, 27, 34, 0.8)',
        padding: '6px 12px',
        borderRadius: 4,
        border: '1px solid #30363D',
      }}
    >
      <span
        style={{
          fontFamily: MONO_FONT,
          fontSize: TERMINAL_FONT_SIZE,
          color: TERMINAL_GREEN,
          letterSpacing: 0.5,
        }}
      >
        pdd generate ✓
      </span>
    </div>
  );
};

/** Block reveal: fades in a group of new code lines */
const BlockReveal: React.FC<{
  lines: CodeLine[];
  startLineNumber: number;
}> = ({ lines, startLineNumber }) => {
  const frame = useCurrentFrame(); // relative to parent Sequence

  const opacity = interpolate(frame, [0, BLOCK_REVEAL_DURATION], [0, 1], {
    easing: Easing.out(Easing.cubic),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <>
      {lines.map((line, i) => (
        <SyntaxLine
          key={startLineNumber + i}
          line={line}
          lineNumber={startLineNumber + i}
          yOffset={TAB_BAR_HEIGHT + (startLineNumber + i - 1) * LINE_HEIGHT}
          opacity={opacity}
        />
      ))}
    </>
  );
};

// ── Main Component ──────────────────────────────────

export const ColdOpen05CodeBlink: React.FC = () => {
  const frame = useCurrentFrame();

  const showOldCode = frame < T_DISSOLVE_START;
  const showCursor =
    frame < T_DISSOLVE_START || frame >= T_VOID_END;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG,
        width: WIDTH,
        height: HEIGHT,
        overflow: 'hidden',
      }}
    >
      {/* IDE chrome (always visible) */}
      <IDEChrome absoluteFrame={frame} />

      {/* ── Phase 1: Old code (frames 0–59) ── */}
      {showOldCode && (
        <AbsoluteFill>
          {OLD_CODE.map((line, i) => (
            <SyntaxLine
              key={`old-${i}`}
              line={line}
              lineNumber={i + 1}
              yOffset={TAB_BAR_HEIGHT + i * LINE_HEIGHT}
            />
          ))}
        </AbsoluteFill>
      )}

      {/* ── Phase 2: Selection highlight sweep (frames 30–59) ── */}
      <Sequence
        from={T_SELECTION_START}
        durationInFrames={T_DISSOLVE_START - T_SELECTION_START}
        layout="none"
      >
        <SelectionHighlight />
      </Sequence>

      {/* ── Phase 3: Particle dissolution (frames 60–104) ── */}
      <Sequence
        from={T_DISSOLVE_START}
        durationInFrames={PARTICLE_FADE_DURATION}
        layout="none"
      >
        <ParticleDissolve />
      </Sequence>

      {/* ── Phase 4: Empty editor with line numbers (frames 60–104) ── */}
      <Sequence
        from={T_DISSOLVE_START}
        durationInFrames={T_VOID_END - T_DISSOLVE_START}
        layout="none"
      >
        <EmptyLineNumbers count={18} />
      </Sequence>

      {/* ── Phase 5: New code block 1 (lines 1–5, frames 105+) ── */}
      <Sequence from={T_BLOCK1} layout="none">
        <BlockReveal lines={NEW_CODE.slice(0, 5)} startLineNumber={1} />
      </Sequence>

      {/* ── New code block 2 (lines 6–10, frames 120+) ── */}
      <Sequence from={T_BLOCK2} layout="none">
        <BlockReveal lines={NEW_CODE.slice(5, 10)} startLineNumber={6} />
      </Sequence>

      {/* ── New code block 3 (lines 11–14, frames 135+) ── */}
      <Sequence from={T_BLOCK3} layout="none">
        <BlockReveal lines={NEW_CODE.slice(10, 14)} startLineNumber={11} />
      </Sequence>

      {/* ── Phase 6: Terminal snippet (frames 150+) ── */}
      <Sequence from={T_TERMINAL} layout="none">
        <TerminalSnippet />
      </Sequence>

      {/* ── Cursor (visible during old code & new code phases) ── */}
      {showCursor && (
        <Cursor
          x={EDITOR_LEFT}
          y={TAB_BAR_HEIGHT + 2}
          absoluteFrame={frame}
        />
      )}
    </AbsoluteFill>
  );
};

export default ColdOpen05CodeBlink;
