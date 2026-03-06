import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { ParticleStream } from "./ParticleStream";
import { ValueBar } from "./ValueBar";
import {
  PANEL_X,
  PANEL_Y,
  PANEL_W,
  PANEL_H,
  PANEL_BORDER_RADIUS,
  PANEL_BG,
  PANEL_BLUR,
  PANEL_FADE_IN_START,
  PANEL_FADE_IN_END,
  PART_CENTER_X,
  PART_CENTER_Y,
  PART_W,
  PART_H,
  PART_INITIAL_FILL,
  PART_FINAL_FILL,
  PART_INITIAL_BORDER,
  PART_FINAL_BORDER,
  PART_LABEL_INITIAL_COLOR,
  PART_LABEL_FINAL_COLOR,
  MOLD_CENTER_X,
  MOLD_CENTER_Y,
  MOLD_W,
  MOLD_H,
  MOLD_INITIAL_FILL,
  MOLD_FINAL_FILL,
  MOLD_BORDER_COLOR,
  MOLD_LABEL_COLOR,
  MOLD_LABEL_BRIGHT_COLOR,
  MOLD_GLOW_MAX_SPREAD,
  MOLD_GLOW_OPACITY,
  DIM_BRIGHTEN_START,
  DIM_BRIGHTEN_END,
  VALUE_BAR_ANIM_END,
  LABEL_BOLD_FRAME,
  FADEOUT_START,
  FADEOUT_END,
  GLOW_PULSE_SPEED,
  BG_COLOR,
} from "./constants";

/** Lerp between two hex colors */
function lerpColor(
  frame: number,
  inputRange: [number, number],
  colors: [string, string]
): string {
  const t = interpolate(frame, inputRange, [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const parse = (hex: string) => {
    const h = hex.replace("#", "");
    return [
      parseInt(h.substring(0, 2), 16),
      parseInt(h.substring(2, 4), 16),
      parseInt(h.substring(4, 6), 16),
    ];
  };

  const [r1, g1, b1] = parse(colors[0]);
  const [r2, g2, b2] = parse(colors[1]);
  const r = Math.round(r1 + (r2 - r1) * t);
  const g = Math.round(g1 + (g2 - g1) * t);
  const b = Math.round(b1 + (b2 - b1) * t);

  return `rgb(${r}, ${g}, ${b})`;
}

export const defaultPart2ParadigmShift05ValueMigrationDiagramProps = {};

export const Part2ParadigmShift05ValueMigrationDiagram: React.FC = () => {
  const frame = useCurrentFrame();

  // --- Panel opacity ---
  const panelAppear = interpolate(
    frame,
    [PANEL_FADE_IN_START, PANEL_FADE_IN_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const panelFadeOut = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const panelOpacity = panelAppear * panelFadeOut;

  // --- Part icon animations ---
  const partScale = interpolate(
    frame,
    [DIM_BRIGHTEN_START, DIM_BRIGHTEN_END],
    [1.0, 0.7],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.quad),
    }
  );
  const partOpacity = interpolate(
    frame,
    [DIM_BRIGHTEN_START, DIM_BRIGHTEN_END],
    [1.0, 0.4],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );
  const partFill = lerpColor(
    frame,
    [DIM_BRIGHTEN_START, DIM_BRIGHTEN_END],
    [PART_INITIAL_FILL, PART_FINAL_FILL]
  );
  const partBorder = lerpColor(
    frame,
    [DIM_BRIGHTEN_START, DIM_BRIGHTEN_END],
    [PART_INITIAL_BORDER, PART_FINAL_BORDER]
  );
  const partLabelColor = lerpColor(
    frame,
    [DIM_BRIGHTEN_START, DIM_BRIGHTEN_END],
    [PART_LABEL_INITIAL_COLOR, PART_LABEL_FINAL_COLOR]
  );

  // --- Mold icon animations ---
  const moldScale = interpolate(
    frame,
    [DIM_BRIGHTEN_START, DIM_BRIGHTEN_END],
    [0.8, 1.1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.quad),
    }
  );
  const moldFill = lerpColor(
    frame,
    [DIM_BRIGHTEN_START, DIM_BRIGHTEN_END],
    [MOLD_INITIAL_FILL, MOLD_FINAL_FILL]
  );
  const moldGlowRadius = interpolate(
    frame,
    [DIM_BRIGHTEN_END, VALUE_BAR_ANIM_END],
    [0, MOLD_GLOW_MAX_SPREAD],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Pulsing glow after particles settle
  const glowPulseOpacity =
    frame > VALUE_BAR_ANIM_END
      ? interpolate(
          Math.sin(frame * GLOW_PULSE_SPEED),
          [-1, 1],
          [0.2, MOLD_GLOW_OPACITY]
        )
      : interpolate(
          frame,
          [DIM_BRIGHTEN_END, VALUE_BAR_ANIM_END],
          [0, MOLD_GLOW_OPACITY],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
        );

  // Mold label styling
  const moldLabelColor = lerpColor(
    frame,
    [DIM_BRIGHTEN_START, DIM_BRIGHTEN_END],
    [MOLD_LABEL_COLOR, MOLD_LABEL_BRIGHT_COLOR]
  );
  const isBold = frame >= LABEL_BOLD_FRAME;

  // Master fade-out for icons layer
  const iconsFadeOut = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part2_paradigm_shift.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Backing panel */}
      <div
        style={{
          position: "absolute",
          left: PANEL_X,
          top: PANEL_Y,
          width: PANEL_W,
          height: PANEL_H,
          borderRadius: PANEL_BORDER_RADIUS,
          background: PANEL_BG,
          backdropFilter: `blur(${PANEL_BLUR}px)`,
          opacity: panelOpacity,
        }}
      />

      {/* Icons layer — SVG for shapes and labels */}
      <AbsoluteFill style={{ opacity: iconsFadeOut }}>
        <svg
          width={1920}
          height={1080}
          viewBox="0 0 1920 1080"
          style={{ position: "absolute", top: 0, left: 0 }}
        >
          <defs>
            <filter id="moldGlow">
              <feGaussianBlur
                in="SourceGraphic"
                stdDeviation={moldGlowRadius}
              />
            </filter>
          </defs>

          {/* === THE PART (bottom icon) === */}
          <g
            transform={`translate(${PART_CENTER_X}, ${PART_CENTER_Y}) scale(${partScale})`}
            opacity={partOpacity}
          >
            <rect
              x={-PART_W / 2}
              y={-PART_H / 2}
              width={PART_W}
              height={PART_H}
              rx={10}
              ry={10}
              fill={partFill}
              stroke={partBorder}
              strokeWidth={2}
            />
            {/* Small detail lines to suggest a "part" */}
            <line
              x1={-PART_W / 4}
              y1={-PART_H / 6}
              x2={PART_W / 4}
              y2={-PART_H / 6}
              stroke={partBorder}
              strokeWidth={1.5}
              opacity={0.6}
            />
            <line
              x1={-PART_W / 4}
              y1={PART_H / 6}
              x2={PART_W / 4}
              y2={PART_H / 6}
              stroke={partBorder}
              strokeWidth={1.5}
              opacity={0.6}
            />
          </g>

          {/* THE PART label */}
          <text
            x={PART_CENTER_X}
            y={PART_CENTER_Y + PART_H / 2 + 30}
            fill={partLabelColor}
            fontSize={18}
            fontFamily="Inter, sans-serif"
            fontWeight={600}
            textAnchor="middle"
            opacity={
              interpolate(
                frame,
                [PANEL_FADE_IN_START, PANEL_FADE_IN_END],
                [0, 1],
                { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
              ) * partOpacity
            }
          >
            THE PART
          </text>

          {/* === THE MOLD (top icon) — document/blueprint shape === */}
          {/* Glow behind mold icon */}
          <rect
            x={MOLD_CENTER_X - MOLD_W / 2 - 10}
            y={MOLD_CENTER_Y - MOLD_H / 2 - 10}
            width={MOLD_W + 20}
            height={MOLD_H + 20}
            rx={8}
            fill={MOLD_BORDER_COLOR}
            opacity={glowPulseOpacity}
            filter="url(#moldGlow)"
          />

          <g
            transform={`translate(${MOLD_CENTER_X}, ${MOLD_CENTER_Y}) scale(${moldScale})`}
          >
            {/* Document shape with folded corner */}
            <path
              d={`M ${-MOLD_W / 2} ${-MOLD_H / 2}
                  L ${MOLD_W / 2 - 20} ${-MOLD_H / 2}
                  L ${MOLD_W / 2} ${-MOLD_H / 2 + 20}
                  L ${MOLD_W / 2} ${MOLD_H / 2}
                  L ${-MOLD_W / 2} ${MOLD_H / 2}
                  Z`}
              fill={moldFill}
              stroke={MOLD_BORDER_COLOR}
              strokeWidth={2}
            />
            {/* Folded corner */}
            <path
              d={`M ${MOLD_W / 2 - 20} ${-MOLD_H / 2}
                  L ${MOLD_W / 2 - 20} ${-MOLD_H / 2 + 20}
                  L ${MOLD_W / 2} ${-MOLD_H / 2 + 20}`}
              fill="none"
              stroke={MOLD_BORDER_COLOR}
              strokeWidth={1.5}
              opacity={0.7}
            />
            {/* Blueprint lines inside document */}
            <line
              x1={-MOLD_W / 2 + 16}
              y1={-MOLD_H / 2 + 28}
              x2={MOLD_W / 2 - 30}
              y2={-MOLD_H / 2 + 28}
              stroke={MOLD_BORDER_COLOR}
              strokeWidth={2}
              opacity={0.5}
            />
            <line
              x1={-MOLD_W / 2 + 16}
              y1={-MOLD_H / 2 + 44}
              x2={MOLD_W / 2 - 16}
              y2={-MOLD_H / 2 + 44}
              stroke={MOLD_BORDER_COLOR}
              strokeWidth={2}
              opacity={0.4}
            />
            <line
              x1={-MOLD_W / 2 + 16}
              y1={-MOLD_H / 2 + 60}
              x2={MOLD_W / 2 - 16}
              y2={-MOLD_H / 2 + 60}
              stroke={MOLD_BORDER_COLOR}
              strokeWidth={2}
              opacity={0.3}
            />
            {/* Small box — cavity diagram */}
            <rect
              x={-MOLD_W / 2 + 16}
              y={MOLD_H / 2 - 30}
              width={32}
              height={20}
              rx={3}
              fill="none"
              stroke={MOLD_BORDER_COLOR}
              strokeWidth={1.5}
              opacity={0.4}
            />
          </g>

          {/* THE MOLD label */}
          <text
            x={MOLD_CENTER_X}
            y={MOLD_CENTER_Y - MOLD_H / 2 * moldScale - 18}
            fill={moldLabelColor}
            fontSize={20}
            fontFamily="Inter, sans-serif"
            fontWeight={isBold ? 800 : 700}
            textAnchor="middle"
            opacity={interpolate(
              frame,
              [PANEL_FADE_IN_START, PANEL_FADE_IN_END],
              [0, 1],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            )}
            textDecoration={isBold ? "underline" : "none"}
          >
            THE MOLD
          </text>
        </svg>
      </AbsoluteFill>

      {/* Migration particle stream */}
      <ParticleStream />

      {/* Value bar */}
      <ValueBar />
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift05ValueMigrationDiagram;
