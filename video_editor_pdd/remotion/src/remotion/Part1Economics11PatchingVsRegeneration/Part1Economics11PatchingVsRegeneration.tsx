import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import {
  BACKGROUND_COLOR,
  LEFT_PANEL_X,
  LEFT_PANEL_Y,
  RIGHT_PANEL_X,
  RIGHT_PANEL_Y,
  PANEL_WIDTH,
  PANEL_HEIGHT,
  PANEL_PADDING,
  COLOR_LEFT_BORDER,
  COLOR_LEFT_HEADER,
  COLOR_RIGHT_BORDER,
  COLOR_RIGHT_HEADER,
  COLOR_PROMPT_BLOCK,
  COLOR_TEST_BLOCK,
  COLOR_GROUNDING_BLOCK,
  COLOR_RED_LABEL,
  COLOR_GREEN_LABEL,
  COLOR_ROOM_TEXT,
  COLOR_DEEP_FILL,
  PROMPT_BLOCK_HEIGHT,
  TEST_BLOCK_HEIGHT,
  GROUNDING_BLOCK_HEIGHT,
  RIGHT_PROMPT_START,
  RIGHT_TESTS_START,
  RIGHT_GROUNDING_START,
  RIGHT_ROOM_START,
  LABELS_APPEAR_START,
  LABEL_FADE_DURATION,
  FONT_FAMILY,
  COMPARISON_LABEL_FONT_SIZE,
} from './constants';
import ContextWindowPanel from './ContextWindowPanel';
import TokenBlockGrid from './TokenBlockGrid';
import CuratedBlock from './CuratedBlock';

export const defaultPart1Economics11PatchingVsRegenerationProps = {};

export const Part1Economics11PatchingVsRegeneration: React.FC = () => {
  const frame = useCurrentFrame();

  // ─── Comparison labels fade in ───
  const labelOpacity = interpolate(
    frame,
    [LABELS_APPEAR_START, LABELS_APPEAR_START + LABEL_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // ─── "Room to think" label ───
  const roomOpacity = interpolate(
    frame,
    [RIGHT_ROOM_START, RIGHT_ROOM_START + LABEL_FADE_DURATION],
    [0, 0.5],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // ─── Right panel deep fill (empty space background) ───
  const rightFillOpacity = interpolate(
    frame,
    [RIGHT_PROMPT_START, RIGHT_PROMPT_START + 30],
    [0, 0.3],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Block vertical offsets inside the right panel
  const promptTop = 0;
  const testTop = PROMPT_BLOCK_HEIGHT + 12;
  const groundingTop = testTop + TEST_BLOCK_HEIGHT + 12;
  const emptySpaceTop = groundingTop + GROUNDING_BLOCK_HEIGHT + 12;
  const emptySpaceHeight =
    PANEL_HEIGHT -
    PANEL_PADDING * 2 -
    emptySpaceTop;

  // Label Y positions (below panels)
  const labelY = LEFT_PANEL_Y + PANEL_HEIGHT + 24;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        fontFamily: FONT_FAMILY,
      }}
    >
      {/* ─── Section Title ─── */}
      <div
        style={{
          position: 'absolute',
          top: 40,
          left: 0,
          width: 1920,
          textAlign: 'center',
          fontFamily: FONT_FAMILY,
          fontSize: 32,
          fontWeight: 700,
          color: '#E2E8F0',
          opacity: interpolate(frame, [0, 30], [0, 0.9], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          }),
        }}
      >
        Context Window Comparison
      </div>

      {/* ─── Subtitle ─── */}
      <div
        style={{
          position: 'absolute',
          top: 86,
          left: 0,
          width: 1920,
          textAlign: 'center',
          fontFamily: FONT_FAMILY,
          fontSize: 16,
          fontWeight: 400,
          color: '#94A3B8',
          opacity: interpolate(frame, [10, 40], [0, 0.7], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          }),
        }}
      >
        What&apos;s inside each approach&apos;s context window?
      </div>

      {/* ─── LEFT PANEL: Agentic Patching ─── */}
      <ContextWindowPanel
        x={LEFT_PANEL_X}
        y={LEFT_PANEL_Y}
        width={PANEL_WIDTH}
        height={PANEL_HEIGHT}
        header="Agentic Patching"
        headerColor={COLOR_LEFT_HEADER}
        borderColor={COLOR_LEFT_BORDER}
        borderStyle="dashed"
      />

      {/* Left panel token block grid */}
      <TokenBlockGrid panelX={LEFT_PANEL_X} panelY={LEFT_PANEL_Y} />

      {/* ─── RIGHT PANEL: PDD Regeneration ─── */}
      <ContextWindowPanel
        x={RIGHT_PANEL_X}
        y={RIGHT_PANEL_Y}
        width={PANEL_WIDTH}
        height={PANEL_HEIGHT}
        header="PDD Regeneration"
        headerColor={COLOR_RIGHT_HEADER}
        borderColor={COLOR_RIGHT_BORDER}
        borderStyle="solid"
      />

      {/* Right panel deep background fill for empty space */}
      <div
        style={{
          position: 'absolute',
          left: RIGHT_PANEL_X + PANEL_PADDING,
          top: RIGHT_PANEL_Y + PANEL_PADDING + emptySpaceTop,
          width: PANEL_WIDTH - PANEL_PADDING * 2,
          height: emptySpaceHeight,
          backgroundColor: COLOR_DEEP_FILL,
          opacity: rightFillOpacity,
          borderRadius: 4,
        }}
      />

      {/* Curated blocks in the right panel */}
      <CuratedBlock
        panelX={RIGHT_PANEL_X}
        panelY={RIGHT_PANEL_Y}
        topOffset={promptTop}
        blockHeight={PROMPT_BLOCK_HEIGHT}
        color={COLOR_PROMPT_BLOCK}
        label="Prompt (300 tokens)"
        slideInStart={RIGHT_PROMPT_START}
      />
      <CuratedBlock
        panelX={RIGHT_PANEL_X}
        panelY={RIGHT_PANEL_Y}
        topOffset={testTop}
        blockHeight={TEST_BLOCK_HEIGHT}
        color={COLOR_TEST_BLOCK}
        label="Tests (2,000 tokens)"
        slideInStart={RIGHT_TESTS_START}
      />
      <CuratedBlock
        panelX={RIGHT_PANEL_X}
        panelY={RIGHT_PANEL_Y}
        topOffset={groundingTop}
        blockHeight={GROUNDING_BLOCK_HEIGHT}
        color={COLOR_GROUNDING_BLOCK}
        label="Grounding example"
        slideInStart={RIGHT_GROUNDING_START}
      />

      {/* "Room to think" label in the empty space */}
      <div
        style={{
          position: 'absolute',
          left: RIGHT_PANEL_X + PANEL_PADDING,
          top:
            RIGHT_PANEL_Y +
            PANEL_PADDING +
            emptySpaceTop +
            emptySpaceHeight / 2 -
            10,
          width: PANEL_WIDTH - PANEL_PADDING * 2,
          textAlign: 'center',
          fontFamily: FONT_FAMILY,
          fontSize: COMPARISON_LABEL_FONT_SIZE,
          fontStyle: 'italic',
          fontWeight: 400,
          color: COLOR_ROOM_TEXT,
          opacity: roomOpacity,
        }}
      >
        Room to think
      </div>

      {/* ─── Comparison Labels ─── */}
      {/* Left label */}
      <div
        style={{
          position: 'absolute',
          left: LEFT_PANEL_X,
          top: labelY,
          width: PANEL_WIDTH,
          textAlign: 'center',
          fontFamily: FONT_FAMILY,
          fontSize: COMPARISON_LABEL_FONT_SIZE,
          fontWeight: 400,
          color: COLOR_RED_LABEL,
          opacity: labelOpacity * 0.85,
        }}
      >
        15,000 tokens — mostly wrong
      </div>

      {/* Right label */}
      <div
        style={{
          position: 'absolute',
          left: RIGHT_PANEL_X,
          top: labelY,
          width: PANEL_WIDTH,
          textAlign: 'center',
          fontFamily: FONT_FAMILY,
          fontSize: COMPARISON_LABEL_FONT_SIZE,
          fontWeight: 400,
          color: COLOR_GREEN_LABEL,
          opacity: labelOpacity * 0.85,
        }}
      >
        2,300 tokens — all curated
      </div>
    </AbsoluteFill>
  );
};

export default Part1Economics11PatchingVsRegeneration;
