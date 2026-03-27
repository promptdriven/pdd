import React, { useMemo } from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from "remotion";
import {
  BG_COLOR,
  MAIN_TEXT_COLOR,
  INSTRUCTION_COLOR,
  ACCENT_COLOR,
  NOISE_OPACITY,
  UNDERLINE_OPACITY,
  INSTRUCTION_OPACITY,
  BOLD_INSTRUCTION_OPACITY,
  MAIN_FONT_SIZE,
  INSTRUCTION_FONT_SIZE,
  INSTRUCTION_LINE_HEIGHT,
  MAIN_TEXT_ROTATION,
  MAIN_TEXT_Y,
  INSTRUCTION_START_Y,
  TOTAL_FRAMES,
  STROKE_WRITE_DURATION,
  UNDERLINE_START,
  UNDERLINE_DURATION,
  INSTRUCTION_LINE1_START,
  INSTRUCTION_LINE2_START,
  INSTRUCTION_LINE3_START,
  INSTRUCTION_FADE_DURATION,
  MAIN_TEXT,
  INSTRUCTIONS,
} from "./constants";

// ── Noise Texture Background ────────────────────────────
const NoiseTexture: React.FC = () => {
  const noiseStyle: React.CSSProperties = useMemo(
    () => ({
      position: "absolute" as const,
      inset: 0,
      opacity: NOISE_OPACITY,
      backgroundImage: `url("data:image/svg+xml,%3Csvg viewBox='0 0 256 256' xmlns='http://www.w3.org/2000/svg'%3E%3Cfilter id='n'%3E%3CfeTurbulence type='fractalNoise' baseFrequency='0.9' numOctaves='4' stitchTiles='stitch'/%3E%3C/filter%3E%3Crect width='100%25' height='100%25' filter='url(%23n)' opacity='1'/%3E%3C/svg%3E")`,
      backgroundSize: "256px 256px",
      mixBlendMode: "overlay" as const,
    }),
    []
  );
  return <div style={noiseStyle} />;
};

// ── Wavy Underline SVG Path ─────────────────────────────
const generateWavyPath = (
  startX: number,
  endX: number,
  y: number,
  amplitude: number,
  frequency: number
): string => {
  const points: string[] = [`M ${startX} ${y}`];
  const step = 4;
  for (let x = startX + step; x <= endX; x += step) {
    const progress = (x - startX) / (endX - startX);
    const yOffset =
      Math.sin(progress * Math.PI * frequency) * amplitude +
      Math.sin(progress * Math.PI * frequency * 2.3) * (amplitude * 0.4);
    points.push(`L ${x} ${y + yOffset}`);
  }
  return points.join(" ");
};

// ── Handwritten Stroke Reveal ───────────────────────────
const HandwrittenText: React.FC<{ frame: number }> = ({ frame }) => {
  const writeProgress = interpolate(frame, [0, STROKE_WRITE_DURATION], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.quad),
  });

  // Use clip-path to reveal text left-to-right like writing
  const clipPercent = writeProgress * 100;

  return (
    <div
      style={{
        position: "absolute",
        top: MAIN_TEXT_Y - MAIN_FONT_SIZE / 2,
        left: 0,
        right: 0,
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
        transform: `rotate(${MAIN_TEXT_ROTATION}deg)`,
      }}
    >
      <div
        style={{
          fontFamily: "'Caveat', cursive, sans-serif",
          fontSize: MAIN_FONT_SIZE,
          color: MAIN_TEXT_COLOR,
          clipPath: `inset(0 ${100 - clipPercent}% 0 0)`,
          whiteSpace: "nowrap",
          lineHeight: 1.2,
        }}
      >
        {MAIN_TEXT}
      </div>
    </div>
  );
};

// ── Animated Wavy Underline ─────────────────────────────
const WavyUnderline: React.FC<{ frame: number }> = ({ frame }) => {
  const localFrame = frame - UNDERLINE_START;
  if (localFrame < 0) return null;

  const drawProgress = interpolate(
    localFrame,
    [0, UNDERLINE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Underline centered beneath the text
  const underlineWidth = 440;
  const startX = (1920 - underlineWidth) / 2;
  const endX = startX + underlineWidth;
  const underlineY = MAIN_TEXT_Y + MAIN_FONT_SIZE / 2 + 10;

  const path = generateWavyPath(startX, endX, underlineY, 3, 4);

  // Calculate total path length estimate for stroke-dasharray
  const totalLength = underlineWidth * 1.05;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <path
        d={path}
        fill="none"
        stroke={ACCENT_COLOR}
        strokeWidth={2.5}
        strokeLinecap="round"
        opacity={UNDERLINE_OPACITY}
        strokeDasharray={totalLength}
        strokeDashoffset={totalLength * (1 - drawProgress)}
        style={{
          transform: `rotate(${MAIN_TEXT_ROTATION}deg)`,
          transformOrigin: "960px 470px",
        }}
      />
    </svg>
  );
};

// ── Instruction Line ────────────────────────────────────
const InstructionLine: React.FC<{
  text: string;
  yOffset: number;
  startFrame: number;
  frame: number;
  isBold?: boolean;
}> = ({ text, yOffset, startFrame, frame, isBold = false }) => {
  const localFrame = frame - startFrame;
  if (localFrame < 0) return null;

  const opacity = interpolate(
    localFrame,
    [0, INSTRUCTION_FADE_DURATION],
    [0, isBold ? BOLD_INSTRUCTION_OPACITY : INSTRUCTION_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const translateY = interpolate(
    localFrame,
    [0, INSTRUCTION_FADE_DURATION],
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
        top: INSTRUCTION_START_Y + yOffset,
        left: 0,
        right: 0,
        textAlign: "center",
        fontFamily: "'Inter', sans-serif",
        fontSize: INSTRUCTION_FONT_SIZE,
        fontWeight: isBold ? 600 : 400,
        color: isBold ? MAIN_TEXT_COLOR : INSTRUCTION_COLOR,
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      {text}
    </div>
  );
};

// ── Main Component ──────────────────────────────────────
export const defaultPart1Economics20TryItYourselfProps = {};

export const Part1Economics20TryItYourself: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Paper texture noise */}
      <NoiseTexture />

      {/* Main handwritten text — visible from frame 0 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <HandwrittenText frame={frame} />
      </Sequence>

      {/* Wavy underline */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <WavyUnderline frame={frame} />
      </Sequence>

      {/* Instruction lines */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <InstructionLine
          text={INSTRUCTIONS[0]}
          yOffset={0}
          startFrame={INSTRUCTION_LINE1_START}
          frame={frame}
        />
        <InstructionLine
          text={INSTRUCTIONS[1]}
          yOffset={INSTRUCTION_LINE_HEIGHT}
          startFrame={INSTRUCTION_LINE2_START}
          frame={frame}
        />
        <InstructionLine
          text={INSTRUCTIONS[2]}
          yOffset={INSTRUCTION_LINE_HEIGHT * 2 + 12}
          startFrame={INSTRUCTION_LINE3_START}
          frame={frame}
          isBold
        />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics20TryItYourself;
