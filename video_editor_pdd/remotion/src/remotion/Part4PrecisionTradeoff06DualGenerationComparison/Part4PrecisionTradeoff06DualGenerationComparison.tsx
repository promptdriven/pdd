import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import MiniPromptFile from './MiniPromptFile';
import TestIndicators from './TestIndicators';
import DownArrow from './DownArrow';
import CodeBlock from './CodeBlock';
import ComparisonBar from './ComparisonBar';
import {
  BG_COLOR,
  AMBER_ACCENT,
  BLUE_ACCENT,
  ARROW_COLOR,
  CODE_BG,
  CODE_GLOW,
  CODE_TEXT_COLOR,
  LABEL_MUTED,
  // Layout
  LEFT_PROMPT_X,
  LEFT_PROMPT_Y,
  LEFT_PROMPT_W,
  LEFT_PROMPT_H,
  RIGHT_PROMPT_X,
  RIGHT_PROMPT_Y,
  RIGHT_PROMPT_W,
  RIGHT_PROMPT_H,
  CODE_BLOCK_W,
  CODE_BLOCK_H,
  LEFT_CODE_X,
  LEFT_CODE_Y,
  RIGHT_CODE_X,
  RIGHT_CODE_Y,
  ARROW_LENGTH,
  LEFT_ARROW_X,
  LEFT_ARROW_TOP,
  RIGHT_ARROW_X,
  RIGHT_ARROW_TOP,
  LEFT_LABEL_X,
  LEFT_LABEL_Y,
  RIGHT_LABEL_X,
  RIGHT_LABEL_Y,
  BAR_Y,
  BAR_WIDTH,
  BAR_CENTER_X,
  BAR_LEFT_WIDTH,
  BAR_RIGHT_WIDTH,
  // Animation frames
  PROMPT_APPEAR_START,
  PROMPT_FADE_DURATION,
  ARROW_DRAW_START,
  ARROW_DRAW_DURATION,
  CODE_GEN_START,
  CODE_LINE_RATE,
  CODE_GLOW_DURATION,
  LABEL_APPEAR_START,
  LABEL_FADE_DURATION,
  BAR_APPEAR_START,
  BAR_ANIM_DURATION,
  FADEOUT_START,
  FADEOUT_DURATION,
  // Data
  TEST_COUNT,
  TEST_DOT_SIZE,
  GENERATED_CODE_LINES,
  FONT_INTER,
} from './constants';

export const defaultPart4PrecisionTradeoff06DualGenerationComparisonProps = {};

export const Part4PrecisionTradeoff06DualGenerationComparison: React.FC = () => {
  const frame = useCurrentFrame();

  // Global fade out at end
  const fadeOut = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_START + FADEOUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  // Label opacity
  const labelOpacity = interpolate(
    frame,
    [LABEL_APPEAR_START, LABEL_APPEAR_START + LABEL_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        opacity: fadeOut,
      }}
    >
      {/* === LEFT COLUMN: 50-line prompt === */}
      <MiniPromptFile
        x={LEFT_PROMPT_X}
        y={LEFT_PROMPT_Y}
        width={LEFT_PROMPT_W}
        height={LEFT_PROMPT_H}
        borderColor={AMBER_ACCENT}
        badge="50 lines"
        lineCount={50}
        appearStart={PROMPT_APPEAR_START}
        appearDuration={PROMPT_FADE_DURATION}
      />

      {/* === RIGHT COLUMN: 10-line prompt + 47 tests === */}
      <MiniPromptFile
        x={RIGHT_PROMPT_X}
        y={RIGHT_PROMPT_Y}
        width={RIGHT_PROMPT_W}
        height={RIGHT_PROMPT_H}
        borderColor={BLUE_ACCENT}
        badge="10 lines"
        lineCount={10}
        appearStart={PROMPT_APPEAR_START}
        appearDuration={PROMPT_FADE_DURATION}
      />

      {/* Test indicator dots surrounding right prompt */}
      <TestIndicators
        count={TEST_COUNT}
        dotSize={TEST_DOT_SIZE}
        color={BLUE_ACCENT}
        dotOpacity={0.5}
        targetX={RIGHT_PROMPT_X}
        targetY={RIGHT_PROMPT_Y}
        targetW={RIGHT_PROMPT_W}
        targetH={RIGHT_PROMPT_H}
        appearStart={PROMPT_APPEAR_START}
        appearDuration={PROMPT_FADE_DURATION}
      />

      {/* === ARROWS === */}
      <DownArrow
        x={LEFT_ARROW_X}
        topY={LEFT_ARROW_TOP}
        length={ARROW_LENGTH}
        color={ARROW_COLOR}
        arrowOpacity={0.5}
        drawStart={ARROW_DRAW_START}
        drawDuration={ARROW_DRAW_DURATION}
      />

      <DownArrow
        x={RIGHT_ARROW_X}
        topY={RIGHT_ARROW_TOP}
        length={ARROW_LENGTH}
        color={ARROW_COLOR}
        arrowOpacity={0.5}
        drawStart={ARROW_DRAW_START}
        drawDuration={ARROW_DRAW_DURATION}
      />

      {/* === CODE BLOCKS === */}
      <CodeBlock
        x={LEFT_CODE_X}
        y={LEFT_CODE_Y}
        width={CODE_BLOCK_W}
        height={CODE_BLOCK_H}
        lines={GENERATED_CODE_LINES}
        genStart={CODE_GEN_START}
        lineRate={CODE_LINE_RATE}
        glowColor={CODE_GLOW}
        glowDuration={CODE_GLOW_DURATION}
        codeTextColor={CODE_TEXT_COLOR}
        codeBgColor={CODE_BG}
      />

      <CodeBlock
        x={RIGHT_CODE_X}
        y={RIGHT_CODE_Y}
        width={CODE_BLOCK_W}
        height={CODE_BLOCK_H}
        lines={GENERATED_CODE_LINES}
        genStart={CODE_GEN_START}
        lineRate={CODE_LINE_RATE}
        glowColor={CODE_GLOW}
        glowDuration={CODE_GLOW_DURATION}
        codeTextColor={CODE_TEXT_COLOR}
        codeBgColor={CODE_BG}
      />

      {/* === COLUMN LABELS === */}
      <div
        style={{
          position: 'absolute',
          left: LEFT_LABEL_X,
          top: LEFT_LABEL_Y,
          transform: 'translateX(-50%)',
          fontFamily: FONT_INTER,
          fontSize: 13,
          color: AMBER_ACCENT,
          opacity: labelOpacity * 0.78,
          whiteSpace: 'nowrap',
        }}
      >
        50-line prompt → Correct code
      </div>

      <div
        style={{
          position: 'absolute',
          left: RIGHT_LABEL_X,
          top: RIGHT_LABEL_Y,
          transform: 'translateX(-50%)',
          fontFamily: FONT_INTER,
          fontSize: 13,
          color: BLUE_ACCENT,
          opacity: labelOpacity * 0.78,
          whiteSpace: 'nowrap',
        }}
      >
        10-line prompt + 47 tests → Same correct code
      </div>

      {/* === COMPARISON BAR === */}
      <ComparisonBar
        centerX={BAR_CENTER_X}
        y={BAR_Y}
        totalWidth={BAR_WIDTH}
        leftWidth={BAR_LEFT_WIDTH}
        rightWidth={BAR_RIGHT_WIDTH}
        leftColor={AMBER_ACCENT}
        rightColor={BLUE_ACCENT}
        label="Prompt effort: 50 lines vs 10 lines"
        callout="5× less"
        calloutColor={BLUE_ACCENT}
        labelColor={LABEL_MUTED}
        appearStart={BAR_APPEAR_START}
        appearDuration={BAR_ANIM_DURATION}
      />
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff06DualGenerationComparison;
