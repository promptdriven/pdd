import React from "react";
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { NoiseTexture } from "./NoiseTexture";
import { HandwrittenText } from "./HandwrittenText";
import { WavyUnderline } from "./WavyUnderline";
import {
  BG_COLOR,
  MAIN_TEXT_COLOR,
  ACCENT_COLOR,
  NOISE_COLOR,
  NOISE_OPACITY,
  MAIN_FONT_SIZE,
  INSTRUCTION_FONT_SIZE,
  INSTRUCTION_LINE_HEIGHT,
  MAIN_TEXT_Y,
  INSTRUCTION_START_Y,
  MAIN_TEXT_ROTATION,
  STROKE_WRITE_START,
  STROKE_WRITE_END,
  UNDERLINE_START,
  UNDERLINE_DURATION,
  UNDERLINE_OPACITY,
  INSTRUCTION_FADE_DURATION,
  INSTRUCTION_LINES,
  TOTAL_DURATION,
} from "./constants";

// ── Default props (empty — this is a self-contained title card) ──
export const defaultPart1Economics20TryItYourselfProps = {};

// ── Instruction Line Sub-Component ──
interface InstructionLineProps {
  text: string;
  weight: number;
  color: string;
  opacity: number;
  startFrame: number;
  fadeDuration: number;
  yPosition: number;
}

const InstructionLine: React.FC<InstructionLineProps> = ({
  text,
  weight,
  color,
  opacity,
  startFrame,
  fadeDuration,
  yPosition,
}) => {
  const frame = useCurrentFrame();

  const lineOpacity = interpolate(
    frame,
    [startFrame, startFrame + fadeDuration],
    [0, opacity],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const translateY = interpolate(
    frame,
    [startFrame, startFrame + fadeDuration],
    [8, 0],
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
        top: yPosition,
        left: 0,
        width: 1920,
        textAlign: "center",
        opacity: lineOpacity,
        transform: `translateY(${translateY}px)`,
        fontFamily: "'Inter', 'Helvetica Neue', Arial, sans-serif",
        fontSize: INSTRUCTION_FONT_SIZE,
        fontWeight: weight,
        color,
        lineHeight: `${INSTRUCTION_LINE_HEIGHT}px`,
        pointerEvents: "none",
      }}
    >
      {text}
    </div>
  );
};

// ── Main Component ──
export const Part1Economics20TryItYourself: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Paper texture noise grain */}
      <NoiseTexture color={NOISE_COLOR} opacity={NOISE_OPACITY} />

      {/* Handwritten "Try it yourself." with stroke-reveal animation */}
      <Sequence from={STROKE_WRITE_START} durationInFrames={TOTAL_DURATION}>
        <HandwrittenText
          text="Try it yourself."
          fontSize={MAIN_FONT_SIZE}
          color={MAIN_TEXT_COLOR}
          centerX={960}
          centerY={MAIN_TEXT_Y}
          rotation={MAIN_TEXT_ROTATION}
          strokeWriteStart={STROKE_WRITE_START}
          strokeWriteEnd={STROKE_WRITE_END}
        />
      </Sequence>

      {/* Wavy underline */}
      <Sequence from={0} durationInFrames={TOTAL_DURATION}>
        <WavyUnderline
          centerX={960}
          y={MAIN_TEXT_Y + 30}
          width={420}
          color={ACCENT_COLOR}
          opacity={UNDERLINE_OPACITY}
          strokeWidth={2}
          startFrame={UNDERLINE_START}
          duration={UNDERLINE_DURATION}
        />
      </Sequence>

      {/* Instruction text lines — fade in sequentially */}
      <Sequence from={0} durationInFrames={TOTAL_DURATION}>
        {INSTRUCTION_LINES.map((line, i) => (
          <InstructionLine
            key={i}
            text={line.text}
            weight={line.weight}
            color={line.color}
            opacity={line.opacity}
            startFrame={line.startFrame}
            fadeDuration={INSTRUCTION_FADE_DURATION}
            yPosition={INSTRUCTION_START_Y + i * INSTRUCTION_LINE_HEIGHT}
          />
        ))}
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics20TryItYourself;
