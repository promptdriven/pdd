import React from "react";
import { useCurrentFrame, interpolate, Easing, interpolateColors } from "remotion";
import { BEATS, COLORS, PART_SHAPE, CODE_LINES } from "./constants";

/**
 * Renders the plastic part that morphs into code lines.
 * During setup (frame 0-90): amber rounded rectangle below the mold.
 * During morph (frame 90-240): stretches into horizontal lines, amber -> gray.
 * During labels (frame 240-360): lines become readable code text.
 * Final state: gray monospace code, no glow.
 */
export const CodeLines: React.FC = () => {
  const frame = useCurrentFrame();

  // Morph progress: 0 at MORPH_START, 1 at MORPH_END
  const morphProgress = interpolate(
    frame,
    [BEATS.MORPH_START, BEATS.MORPH_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Color transition: amber -> gray (easeOutQuad)
  const colorProgress = interpolate(
    frame,
    [BEATS.MORPH_START, BEATS.MORPH_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Code text readability transition (labels phase)
  const textOpacity = interpolate(
    frame,
    [BEATS.LABELS_START, BEATS.LABELS_START + 60],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Line bars opacity (inverse of text — bars fade as text appears)
  const barsOpacity = interpolate(
    frame,
    [BEATS.LABELS_START, BEATS.LABELS_START + 60],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Interpolate the part shape
  const partX = interpolate(morphProgress, [0, 1], [PART_SHAPE.initialX, PART_SHAPE.finalX]);
  const partY = interpolate(morphProgress, [0, 1], [PART_SHAPE.initialY, PART_SHAPE.finalY]);
  const partWidth = interpolate(morphProgress, [0, 1], [PART_SHAPE.initialWidth, PART_SHAPE.finalWidth]);
  const partHeight = interpolate(morphProgress, [0, 1], [PART_SHAPE.initialHeight, PART_SHAPE.finalHeight]);
  const partRx = interpolate(morphProgress, [0, 1], [PART_SHAPE.initialRx, PART_SHAPE.finalRx]);

  // Background color for the code region
  const bgColor = interpolateColors(
    colorProgress,
    [0, 1],
    [COLORS.PART_AMBER, "#1E1E2A"]
  );

  const bgOpacity = interpolate(colorProgress, [0, 1], [1, 0.6]);

  // Line color transitions from amber to gray
  const lineColor = interpolateColors(
    colorProgress,
    [0, 1],
    [COLORS.PART_AMBER_LIGHT, COLORS.CODE_GRAY]
  );

  // Individual code line bars (appear during morph, replace initial solid block)
  const lineBarProgress = interpolate(
    morphProgress,
    [0.3, 0.8],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Compute line widths based on actual code line lengths (proportional)
  const maxLineLength = Math.max(...CODE_LINES.map((l) => l.length));
  const lineWidths = CODE_LINES.map(
    (l) => (l.length / maxLineLength) * (partWidth - 40)
  );

  return (
    <>
      {/* Part background (amber block morphing to dark code background) */}
      <rect
        x={partX}
        y={partY}
        width={partWidth}
        height={partHeight}
        rx={partRx}
        fill={bgColor}
        opacity={bgOpacity}
      />

      {/* Horizontal line bars representing code structure (visible during morph) */}
      {lineBarProgress > 0 && barsOpacity > 0 && (
        <g opacity={barsOpacity}>
          {CODE_LINES.map((_, i) => {
            const lineY = partY + 25 + i * 28;
            const barWidth = lineWidths[i] * lineBarProgress;
            // Stagger each line slightly
            const lineProgress = interpolate(
              morphProgress,
              [0.3 + i * 0.05, 0.8 + i * 0.02],
              [0, 1],
              {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
              }
            );

            return (
              <rect
                key={`bar-${i}`}
                x={partX + 20}
                y={lineY}
                width={barWidth * lineProgress}
                height={4}
                rx={2}
                fill={lineColor}
                opacity={0.8}
              />
            );
          })}
        </g>
      )}

      {/* Actual code text (fades in during labels phase) */}
      {textOpacity > 0 && (
        <g opacity={textOpacity}>
          {CODE_LINES.map((line, i) => {
            const lineY = partY + 32 + i * 28;
            // Stagger each line
            const lineDelay = i * 5;
            const lineOpacity = interpolate(
              frame,
              [BEATS.LABELS_START + lineDelay, BEATS.LABELS_START + 50 + lineDelay],
              [0, 1],
              {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
                easing: Easing.out(Easing.cubic),
              }
            );

            return (
              <text
                key={`code-${i}`}
                x={partX + 20}
                y={lineY}
                fontSize={14}
                fontFamily="'JetBrains Mono', 'Fira Code', 'Courier New', monospace"
                fontWeight={400}
                fill={COLORS.CODE_GRAY}
                opacity={lineOpacity}
              >
                {line}
              </text>
            );
          })}
        </g>
      )}
    </>
  );
};
