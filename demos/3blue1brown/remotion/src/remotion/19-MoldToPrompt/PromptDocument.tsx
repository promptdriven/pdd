import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { BEATS, COLORS, VERILOG_BLOCK, PROMPT_TITLE, PROMPT_LINES } from "./constants";

/**
 * Renders the prompt document text content that fades in during the labels phase.
 * Title "PROMPT" centered at top, body text below divider.
 * Positioned to align with the final document shape from VerilogBlock.
 */
export const PromptDocument: React.FC = () => {
  const frame = useCurrentFrame();

  // Title fade-in: starts at LABELS_START, fully visible by LABELS_START + 40
  const titleOpacity = interpolate(
    frame,
    [BEATS.LABELS_START, BEATS.LABELS_START + 40],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Body text fades in slightly after title
  const bodyOpacity = interpolate(
    frame,
    [BEATS.LABELS_START + 20, BEATS.LABELS_START + 60],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Slight upward slide for title
  const titleSlideY = interpolate(
    frame,
    [BEATS.LABELS_START, BEATS.LABELS_START + 40],
    [8, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  if (frame < BEATS.LABELS_START) return null;

  const docX = VERILOG_BLOCK.finalX;
  const docY = VERILOG_BLOCK.finalY;
  const docWidth = VERILOG_BLOCK.finalWidth;

  return (
    <g>
      {/* PROMPT title */}
      <text
        x={docX + docWidth / 2}
        y={docY + 40 + titleSlideY}
        textAnchor="middle"
        fontSize={24}
        fontFamily="'Inter', 'Helvetica Neue', Arial, sans-serif"
        fontWeight={700}
        fill={COLORS.PROMPT_TITLE_COLOR}
        opacity={titleOpacity}
        letterSpacing={3}
      >
        {PROMPT_TITLE}
      </text>

      {/* Prompt body text */}
      {PROMPT_LINES.map((line, i) => {
        // Stagger each line slightly
        const lineDelay = i * 4;
        const lineOpacity = interpolate(
          frame,
          [BEATS.LABELS_START + 20 + lineDelay, BEATS.LABELS_START + 60 + lineDelay],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          }
        );

        if (line === "") return null;

        // Bold styling for "Requirements:" line
        const isBold = line === "Requirements:";
        const isBullet = line.startsWith("-");

        return (
          <text
            key={i}
            x={docX + 30 + (isBullet ? 10 : 0)}
            y={docY + 95 + i * 30}
            fontSize={isBold ? 16 : 15}
            fontFamily="'Inter', 'Helvetica Neue', Arial, sans-serif"
            fontWeight={isBold ? 600 : 400}
            fill={COLORS.PROMPT_TEXT_COLOR}
            opacity={Math.min(bodyOpacity, lineOpacity)}
          >
            {line}
          </text>
        );
      })}
    </g>
  );
};
