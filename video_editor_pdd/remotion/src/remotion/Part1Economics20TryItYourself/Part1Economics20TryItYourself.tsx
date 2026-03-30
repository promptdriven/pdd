// Part1Economics20TryItYourself.tsx
// Handwritten challenge card: "Try it yourself." with instruction text.
import React from "react";
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";

import NoiseTexture from "./NoiseTexture";
import StrokeRevealText from "./StrokeRevealText";
import WavyUnderline from "./WavyUnderline";
import {
  BACKGROUND_COLOR,
  NOISE_COLOR,
  NOISE_OPACITY,
  CHALLENGE_TEXT_COLOR,
  CHALLENGE_FONT_SIZE,
  CHALLENGE_FONT_FAMILY,
  CHALLENGE_Y,
  CHALLENGE_ROTATION_DEG,
  UNDERLINE_COLOR,
  UNDERLINE_OPACITY,
  INSTRUCTION_DIM_COLOR,
  INSTRUCTION_BOLD_COLOR,
  INSTRUCTION_DIM_OPACITY,
  INSTRUCTION_BOLD_OPACITY,
  INSTRUCTION_FONT_SIZE,
  INSTRUCTION_FONT_FAMILY,
  INSTRUCTION_LINE_HEIGHT,
  INSTRUCTION_START_Y,
  CANVAS_WIDTH,
  STROKE_START,
  STROKE_DURATION,
  UNDERLINE_START,
  UNDERLINE_DURATION,
  LINE1_START,
  LINE2_START,
  LINE3_START,
  LINE_FADE_DURATION,
  INSTRUCTIONS,
  TOTAL_FRAMES,
} from "./constants";

// ─── Instruction Line ─────────────────────────────────────────

interface InstructionLineProps {
  text: string;
  bold: boolean;
  y: number;
  startFrame: number;
  fadeDuration: number;
}

const InstructionLine: React.FC<InstructionLineProps> = ({
  text,
  bold,
  y,
  startFrame,
  fadeDuration,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [startFrame, startFrame + fadeDuration],
    [0, bold ? INSTRUCTION_BOLD_OPACITY : INSTRUCTION_DIM_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <div
      style={{
        position: "absolute",
        top: y,
        left: 0,
        width: CANVAS_WIDTH,
        textAlign: "center",
        fontFamily: INSTRUCTION_FONT_FAMILY,
        fontSize: INSTRUCTION_FONT_SIZE,
        fontWeight: bold ? 600 : 400,
        color: bold ? INSTRUCTION_BOLD_COLOR : INSTRUCTION_DIM_COLOR,
        opacity,
        lineHeight: 1,
      }}
    >
      {text}
    </div>
  );
};

// ─── Main Component ───────────────────────────────────────────

export const defaultPart1Economics20TryItYourselfProps = {};

export const Part1Economics20TryItYourself: React.FC = () => {
  const lineStarts = [LINE1_START, LINE2_START, LINE3_START];

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Subtle paper-grain noise overlay */}
      <NoiseTexture color={NOISE_COLOR} opacity={NOISE_OPACITY} />

      {/* "Try it yourself." — stroke-reveal handwritten text */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <StrokeRevealText
          text="Try it yourself."
          fontFamily={CHALLENGE_FONT_FAMILY}
          fontSize={CHALLENGE_FONT_SIZE}
          color={CHALLENGE_TEXT_COLOR}
          centerX={CANVAS_WIDTH / 2}
          centerY={CHALLENGE_Y}
          rotationDeg={CHALLENGE_ROTATION_DEG}
          startFrame={STROKE_START}
          duration={STROKE_DURATION}
        />
      </Sequence>

      {/* Hand-drawn wavy underline */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <WavyUnderline
          centerX={CANVAS_WIDTH / 2}
          y={CHALLENGE_Y + 28}
          width={420}
          color={UNDERLINE_COLOR}
          opacity={UNDERLINE_OPACITY}
          strokeWidth={2}
          startFrame={UNDERLINE_START}
          duration={UNDERLINE_DURATION}
        />
      </Sequence>

      {/* Instruction lines — fade in sequentially */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        {INSTRUCTIONS.map((line, i) => (
          <InstructionLine
            key={i}
            text={line.text}
            bold={line.bold}
            y={INSTRUCTION_START_Y + i * INSTRUCTION_LINE_HEIGHT}
            startFrame={lineStarts[i]}
            fadeDuration={LINE_FADE_DURATION}
          />
        ))}
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics20TryItYourself;
