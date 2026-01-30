import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { MoldShape } from "./MoldShape";
import { PromptDocument } from "./PromptDocument";
import { CodeLines } from "./CodeLines";
import { FlowArrow } from "./FlowArrow";
import { COLORS, BEATS, MoldToPromptPropsType } from "./constants";

/**
 * Main composition for "Mold Morphs to Prompt" (Section 2.10).
 *
 * Animation sequence:
 * 1. Frame 0-90: Setup — mold visible left-center, plastic part below.
 * 2. Frame 90-240: Primary morph — mold flattens to document, part stretches to code.
 * 3. Frame 240-360: Labels — "PROMPT" title, code readable, blue glow.
 * 4. Frame 360-480: Relationship — downward arrow from prompt to code.
 * 5. Frame 480-600: Hold — prompt glowing, code present but not glowing.
 */
export const MoldToPrompt: React.FC<MoldToPromptPropsType> = ({
  showNarration = true,
}) => {
  const frame = useCurrentFrame();

  // Narration fade-in at frame 360
  const narrationOpacity = showNarration
    ? interpolate(
        frame,
        [BEATS.NARRATION_START, BEATS.NARRATION_START + 40],
        [0, 1],
        {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        }
      )
    : 0;

  // Manufacturing context label (fades out as morph begins)
  const contextOpacity = interpolate(
    frame,
    [0, 20, BEATS.MORPH_START, BEATS.MORPH_START + 30],
    [0, 0.6, 0.6, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.BACKGROUND} 0%, ${COLORS.BACKGROUND_GRADIENT_END} 100%)`,
      }}
    >
      {/* SVG canvas for all shapes */}
      <svg
        width="1920"
        height="1080"
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Mold shape morphing to document */}
        <MoldShape />

        {/* Prompt document text content */}
        <PromptDocument />

        {/* Code lines (morphed from plastic part) */}
        <CodeLines />

        {/* Flow arrow from prompt to code */}
        <FlowArrow />
      </svg>

      {/* Manufacturing context label (setup phase only) */}
      {contextOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            top: 180,
            left: 520,
            opacity: contextOpacity,
          }}
        >
          <div
            style={{
              fontSize: 14,
              fontFamily: "sans-serif",
              fontWeight: 500,
              textTransform: "uppercase" as const,
              letterSpacing: 2,
              color: "rgba(255, 255, 255, 0.4)",
            }}
          >
            Injection Mold
          </div>
        </div>
      )}

      {/* Narration overlay at frame 360 */}
      {narrationOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 80,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: narrationOpacity,
          }}
        >
          <div
            style={{
              fontSize: 36,
              fontFamily: "'Inter', 'Helvetica Neue', Arial, sans-serif",
              fontWeight: 500,
              color: COLORS.NARRATION_WHITE,
              lineHeight: 1.5,
              maxWidth: 900,
              margin: "0 auto",
              letterSpacing: 0.5,
            }}
          >
            This is Prompt-Driven Development.
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
