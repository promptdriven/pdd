import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';

import BlueprintGrid from './BlueprintGrid';
import DiffDissolve from './DiffDissolve';
import PromptDocument from './PromptDocument';
import TestSuitePanel from './TestSuitePanel';

import {
  BG_COLOR,
  PANEL_BG,
  GRID_COLOR,
  GRID_OPACITY,
  GRID_SPACING,
  TEXT_PRIMARY,
  AMBER_ACCENT,
  GREEN_ACCENT,
  PANEL_BORDER_RADIUS,
  PANEL_PADDING,
  PROMPT_X,
  PROMPT_Y,
  PROMPT_WIDTH,
  TESTS_X,
  TESTS_Y,
  TESTS_WIDTH,
  LABEL_Y,
  UNDERLINE_Y,
  DISSOLVE_END,
  PROMPT_FADE_START,
  PROMPT_FADE_DURATION,
  TESTS_FADE_START,
  TESTS_FADE_DURATION,
  TEST_ROW_STAGGER,
  LABEL_START,
  LABEL_CHAR_DELAY,
  UNDERLINE_START,
  UNDERLINE_DURATION,
  MORPH_START,
  MORPH_DURATION,
  AURA_BLUR,
  AURA_OPACITY,
  PROMPT_LINES,
  TEST_ROWS,
  LABEL_TEXT,
  DIFF_LINES,
  DURATION_FRAMES,
} from './constants';

// ─── Default props (required export) ─────────────────────────────────────────
export const defaultPart2ParadigmShift17ReviewSpecVerifyOutputProps = {};

// ─── Main Component ──────────────────────────────────────────────────────────
export const Part2ParadigmShift17ReviewSpecVerifyOutput: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Morph progress (frames 240–330 → 0..1) ────────────────────────────────
  const morphProgress = interpolate(
    frame,
    [MORPH_START, MORPH_START + MORPH_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // ── Label typewriter ───────────────────────────────────────────────────────
  const labelRelative = frame - LABEL_START;
  const visibleChars =
    labelRelative < 0
      ? 0
      : Math.min(
          LABEL_TEXT.length,
          Math.floor(labelRelative / LABEL_CHAR_DELAY)
        );
  const labelVisible = LABEL_TEXT.slice(0, visibleChars);

  // ── Underline draw ─────────────────────────────────────────────────────────
  const underlineProgress = interpolate(
    frame,
    [UNDERLINE_START, UNDERLINE_START + UNDERLINE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const underlineHalfWidth = 200; // total width 400px, drawn from center
  const underlineLeft = 960 - underlineHalfWidth * underlineProgress;
  const underlineRight = 960 + underlineHalfWidth * underlineProgress;

  // ── Label opacity ──────────────────────────────────────────────────────────
  const labelOpacity = interpolate(
    frame,
    [LABEL_START, LABEL_START + 10],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Blueprint grid — visible from frame 0 */}
      <BlueprintGrid
        spacing={GRID_SPACING}
        color={GRID_COLOR}
        opacity={GRID_OPACITY}
      />

      {/* Code diff dissolve (frames 0–45) */}
      <Sequence from={0} durationInFrames={DISSOLVE_END + 5}>
        <DiffDissolve lines={DIFF_LINES} dissolveEnd={DISSOLVE_END} />
      </Sequence>

      {/* Prompt document (appears at frame 45) */}
      <PromptDocument
        lines={PROMPT_LINES}
        headerColor={AMBER_ACCENT}
        textColor={TEXT_PRIMARY}
        panelBg={PANEL_BG}
        auraColor={AMBER_ACCENT}
        auraOpacity={AURA_OPACITY}
        auraBlur={AURA_BLUR}
        x={PROMPT_X}
        y={PROMPT_Y}
        width={PROMPT_WIDTH}
        padding={PANEL_PADDING}
        borderRadius={PANEL_BORDER_RADIUS}
        fadeStartFrame={PROMPT_FADE_START}
        fadeDuration={PROMPT_FADE_DURATION}
        morphProgress={morphProgress}
      />

      {/* Test suite panel (appears at frame 105) */}
      <TestSuitePanel
        tests={TEST_ROWS}
        headerColor={GREEN_ACCENT}
        checkColor={GREEN_ACCENT}
        textColor={TEXT_PRIMARY}
        panelBg={PANEL_BG}
        x={TESTS_X}
        y={TESTS_Y}
        width={TESTS_WIDTH}
        padding={PANEL_PADDING}
        borderRadius={PANEL_BORDER_RADIUS}
        fadeStartFrame={TESTS_FADE_START}
        fadeDuration={TESTS_FADE_DURATION}
        rowStagger={TEST_ROW_STAGGER}
        morphProgress={morphProgress}
      />

      {/* Bottom label — typewriter + underline */}
      {labelRelative >= 0 && (
        <div
          style={{
            position: 'absolute',
            left: 0,
            right: 0,
            top: LABEL_Y,
            display: 'flex',
            flexDirection: 'column',
            alignItems: 'center',
            opacity: labelOpacity,
          }}
        >
          {/* Typed text */}
          <div
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 24,
              fontWeight: 700,
              color: TEXT_PRIMARY,
              textAlign: 'center',
              minHeight: 32,
              whiteSpace: 'pre',
            }}
          >
            {labelVisible}
            {/* Blinking cursor while typing */}
            {visibleChars < LABEL_TEXT.length && (
              <span
                style={{
                  opacity: frame % 16 < 8 ? 1 : 0,
                  color: TEXT_PRIMARY,
                }}
              >
                |
              </span>
            )}
          </div>

          {/* Underline drawn from center */}
          {underlineProgress > 0 && (
            <svg
              width={1920}
              height={10}
              viewBox="0 0 1920 10"
              style={{ position: 'absolute', top: UNDERLINE_Y - LABEL_Y }}
            >
              <line
                x1={underlineLeft}
                y1={5}
                x2={underlineRight}
                y2={5}
                stroke={GREEN_ACCENT}
                strokeWidth={2}
                strokeLinecap="round"
                opacity={0.85}
              />
            </svg>
          )}
        </div>
      )}

      {/* Morph overlay effect — subtle glow pulse during morph phase */}
      {morphProgress > 0 && morphProgress < 1 && (
        <AbsoluteFill
          style={{
            background: `radial-gradient(ellipse at 50% 50%, ${AMBER_ACCENT}08 0%, transparent 70%)`,
            opacity: interpolate(
              morphProgress,
              [0, 0.5, 1],
              [0, 0.3, 0],
              { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
            ),
            pointerEvents: 'none',
          }}
        />
      )}
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift17ReviewSpecVerifyOutput;
