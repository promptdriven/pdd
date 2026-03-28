import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from "remotion";
import MiniPromptFile from "./MiniPromptFile";
import TestIndicators from "./TestIndicators";
import CodeBlock from "./CodeBlock";
import ComparisonBar from "./ComparisonBar";
import {
  BG_COLOR,
  AMBER_ACCENT,
  BLUE_ACCENT,
  CODE_BG,
  GLOW_GREEN,
  ARROW_COLOR,
  CODE_TEXT_COLOR,
  LABEL_MUTED,
  LEFT_PROMPT_X,
  LEFT_PROMPT_Y,
  LEFT_PROMPT_W,
  LEFT_PROMPT_H,
  RIGHT_PROMPT_X,
  RIGHT_PROMPT_Y,
  RIGHT_PROMPT_W,
  RIGHT_PROMPT_H,
  LEFT_CODE_X,
  LEFT_CODE_Y,
  RIGHT_CODE_X,
  RIGHT_CODE_Y,
  CODE_BLOCK_W,
  CODE_BLOCK_H,
  LEFT_ARROW_X,
  LEFT_ARROW_START_Y,
  LEFT_ARROW_END_Y,
  RIGHT_ARROW_X,
  RIGHT_ARROW_START_Y,
  RIGHT_ARROW_END_Y,
  LEFT_LABEL_X,
  RIGHT_LABEL_X,
  LABEL_Y,
  BAR_Y,
  BAR_WIDTH,
  BAR_LEFT_WIDTH,
  BAR_RIGHT_WIDTH,
  TEST_DOT_SIZE,
  TEST_COUNT,
  PROMPT_APPEAR_START,
  PROMPT_FADE_DURATION,
  ARROW_DRAW_START,
  ARROW_DRAW_DURATION,
  CODE_GEN_START,
  CODE_LINE_RATE,
  LABELS_START,
  LABELS_FADE_DURATION,
  BAR_START,
  BAR_ANIM_DURATION,
  FADE_OUT_START,
  FADE_OUT_DURATION,
  TOTAL_FRAMES,
  GENERATED_CODE_LINES,
} from "./constants";

// ─── Arrow Sub-component ───────────────────────────────────────────
const DownArrow: React.FC<{
  x: number;
  startY: number;
  endY: number;
  color: string;
  arrowOpacity: number;
  drawStart: number;
  drawDuration: number;
}> = ({ x, startY, endY, color, arrowOpacity, drawStart, drawDuration }) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [drawStart, drawStart + drawDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const arrowHeight = endY - startY;
  const currentHeight = arrowHeight * progress;
  const headSize = 6;

  return (
    <svg
      style={{
        position: "absolute",
        left: x - 10,
        top: startY,
        width: 20,
        height: arrowHeight + headSize,
        overflow: "visible",
      }}
    >
      {/* Shaft */}
      <line
        x1={10}
        y1={0}
        x2={10}
        y2={currentHeight}
        stroke={color}
        strokeWidth={2}
        opacity={arrowOpacity}
      />
      {/* Arrowhead */}
      {progress > 0.6 && (
        <polygon
          points={`${10 - headSize},${currentHeight - headSize} 10,${currentHeight} ${10 + headSize},${currentHeight - headSize}`}
          fill={color}
          opacity={arrowOpacity * Math.min(1, (progress - 0.6) / 0.4)}
        />
      )}
    </svg>
  );
};

// ─── Column Label Sub-component ────────────────────────────────────
const ColumnLabel: React.FC<{
  text: string;
  color: string;
  centerX: number;
  labelY: number;
  labelStart: number;
  fadeDuration: number;
}> = ({ text, color, centerX, labelY, labelStart, fadeDuration }) => {
  const frame = useCurrentFrame();

  const labelOpacity = interpolate(
    frame,
    [labelStart, labelStart + fadeDuration],
    [0, 0.78],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: centerX - 200,
        top: labelY,
        width: 400,
        textAlign: "center",
        fontFamily: "Inter, sans-serif",
        fontSize: 13,
        fontWeight: 400,
        color,
        opacity: labelOpacity,
      }}
    >
      {text}
    </div>
  );
};

// ─── Main Component ────────────────────────────────────────────────
export const defaultPart4PrecisionTradeoff06DualGenerationComparisonProps = {};

export const Part4PrecisionTradeoff06DualGenerationComparison: React.FC = () => {
  const frame = useCurrentFrame();

  // Global fade out
  const fadeOut = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_START + FADE_OUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        opacity: fadeOut,
      }}
    >
      {/* ─── Section Title ─────────────────────────── */}
      <div
        style={{
          position: "absolute",
          top: 30,
          left: 0,
          right: 0,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 20,
          fontWeight: 600,
          color: "#E2E8F0",
          opacity: interpolate(frame, [0, 20], [0, 0.85], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }),
          letterSpacing: 0.5,
        }}
      >
        Same Output, Different Paths
      </div>

      {/* ─── Center Divider ────────────────────────── */}
      <div
        style={{
          position: "absolute",
          left: 960,
          top: 80,
          width: 2,
          height: 560,
          backgroundColor: "#334155",
          opacity: 0.3,
        }}
      />

      {/* ─── LEFT COLUMN: 50-line prompt ───────────── */}

      {/* Left Column Header */}
      <div
        style={{
          position: "absolute",
          left: LEFT_PROMPT_X - LEFT_PROMPT_W / 2,
          top: 72,
          width: LEFT_PROMPT_W,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 12,
          fontWeight: 600,
          color: AMBER_ACCENT,
          opacity: interpolate(frame, [0, PROMPT_FADE_DURATION], [0, 0.8], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }),
          letterSpacing: 1,
          textTransform: "uppercase",
        }}
      >
        High Prompt Effort
      </div>

      {/* Left Prompt File */}
      <MiniPromptFile
        x={LEFT_PROMPT_X}
        y={LEFT_PROMPT_Y}
        width={LEFT_PROMPT_W}
        height={LEFT_PROMPT_H}
        borderColor={AMBER_ACCENT}
        badge="50 lines"
        lineCount={50}
        appearStart={PROMPT_APPEAR_START}
        fadeDuration={PROMPT_FADE_DURATION}
      />

      {/* Left Arrow */}
      <DownArrow
        x={LEFT_ARROW_X}
        startY={LEFT_ARROW_START_Y}
        endY={LEFT_ARROW_END_Y}
        color={ARROW_COLOR}
        arrowOpacity={0.5}
        drawStart={ARROW_DRAW_START}
        drawDuration={ARROW_DRAW_DURATION}
      />

      {/* Left Code Block */}
      <CodeBlock
        x={LEFT_CODE_X}
        y={LEFT_CODE_Y}
        width={CODE_BLOCK_W}
        height={CODE_BLOCK_H}
        lines={GENERATED_CODE_LINES}
        genStart={CODE_GEN_START}
        lineRate={CODE_LINE_RATE}
        glowColor={GLOW_GREEN}
        bgColor={CODE_BG}
        textColor={CODE_TEXT_COLOR}
        textOpacity={0.7}
      />

      {/* Left Label */}
      <ColumnLabel
        text="50-line prompt → Correct code"
        color={AMBER_ACCENT}
        centerX={LEFT_LABEL_X}
        labelY={LABEL_Y}
        labelStart={LABELS_START}
        fadeDuration={LABELS_FADE_DURATION}
      />

      {/* ─── RIGHT COLUMN: 10-line prompt + tests ─── */}

      {/* Right Column Header */}
      <div
        style={{
          position: "absolute",
          left: RIGHT_PROMPT_X - RIGHT_PROMPT_W / 2 - 60,
          top: 72,
          width: RIGHT_PROMPT_W + 120,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 12,
          fontWeight: 600,
          color: BLUE_ACCENT,
          opacity: interpolate(frame, [0, PROMPT_FADE_DURATION], [0, 0.8], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }),
          letterSpacing: 1,
          textTransform: "uppercase",
        }}
      >
        Low Prompt + Tests
      </div>

      {/* Right Prompt File */}
      <MiniPromptFile
        x={RIGHT_PROMPT_X}
        y={RIGHT_PROMPT_Y}
        width={RIGHT_PROMPT_W}
        height={RIGHT_PROMPT_H}
        borderColor={BLUE_ACCENT}
        badge="10 lines"
        lineCount={10}
        appearStart={PROMPT_APPEAR_START}
        fadeDuration={PROMPT_FADE_DURATION}
      />

      {/* Test Indicators (47 dots around right prompt) */}
      <TestIndicators
        count={TEST_COUNT}
        dotSize={TEST_DOT_SIZE}
        color={BLUE_ACCENT}
        dotOpacity={0.5}
        centerX={RIGHT_PROMPT_X}
        topY={RIGHT_PROMPT_Y}
        promptW={RIGHT_PROMPT_W}
        promptH={RIGHT_PROMPT_H}
        appearStart={PROMPT_APPEAR_START}
        fadeDuration={PROMPT_FADE_DURATION}
      />

      {/* Right Arrow */}
      <DownArrow
        x={RIGHT_ARROW_X}
        startY={RIGHT_ARROW_START_Y}
        endY={RIGHT_ARROW_END_Y}
        color={ARROW_COLOR}
        arrowOpacity={0.5}
        drawStart={ARROW_DRAW_START}
        drawDuration={ARROW_DRAW_DURATION}
      />

      {/* Right Code Block */}
      <CodeBlock
        x={RIGHT_CODE_X}
        y={RIGHT_CODE_Y}
        width={CODE_BLOCK_W}
        height={CODE_BLOCK_H}
        lines={GENERATED_CODE_LINES}
        genStart={CODE_GEN_START}
        lineRate={CODE_LINE_RATE}
        glowColor={GLOW_GREEN}
        bgColor={CODE_BG}
        textColor={CODE_TEXT_COLOR}
        textOpacity={0.7}
      />

      {/* Right Label */}
      <ColumnLabel
        text="10-line prompt + 47 tests → Same correct code"
        color={BLUE_ACCENT}
        centerX={RIGHT_LABEL_X}
        labelY={LABEL_Y}
        labelStart={LABELS_START}
        fadeDuration={LABELS_FADE_DURATION}
      />

      {/* ─── Comparison Bar ────────────────────────── */}
      <ComparisonBar
        barY={BAR_Y}
        totalWidth={BAR_WIDTH}
        leftSegmentWidth={BAR_LEFT_WIDTH}
        rightSegmentWidth={BAR_RIGHT_WIDTH}
        leftColor={AMBER_ACCENT}
        rightColor={BLUE_ACCENT}
        label="Prompt effort: 50 lines vs 10 lines"
        labelColor={LABEL_MUTED}
        callout="5× less"
        calloutColor={BLUE_ACCENT}
        animStart={BAR_START}
        animDuration={BAR_ANIM_DURATION}
      />
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff06DualGenerationComparison;
