import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, GENERATED_CODE, CodeOutputMoldGlowsPropsType } from "./constants";

export const CodeOutputMoldGlows: React.FC<CodeOutputMoldGlowsPropsType> = ({
  showMessages = true,
}) => {
  const frame = useCurrentFrame();

  // Code glow (fades out)
  const codeGlow = interpolate(
    frame,
    [BEATS.CODE_GLOW_START, BEATS.CODE_GLOW_PEAK, BEATS.CODE_GLOW_FADE],
    [0, 1, 0],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Code opacity (dims but stays visible)
  const codeOpacity = interpolate(
    frame,
    [BEATS.CODE_GLOW_START, BEATS.CODE_GLOW_FADE],
    [1, 0.5],
    { extrapolateRight: "clamp" }
  );

  // Mold glow (increases)
  const moldGlow = interpolate(
    frame,
    [BEATS.MOLD_GLOW_START, BEATS.MOLD_GLOW_PEAK],
    [0.3, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Messages
  const message1Opacity = showMessages
    ? interpolate(
        frame,
        [BEATS.MESSAGE_1_START, BEATS.MESSAGE_1_END],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    : 0;

  const message2Opacity = showMessages
    ? interpolate(
        frame,
        [BEATS.MESSAGE_2_START, BEATS.MESSAGE_2_END],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    : 0;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Mold system (three components) */}
      <div
        style={{
          position: "absolute",
          top: 100,
          left: "50%",
          transform: "translateX(-50%)",
        }}
      >
        <div
          style={{
            display: "flex",
            gap: 30,
            justifyContent: "center",
          }}
        >
          {/* Prompt */}
          <div
            style={{
              padding: "12px 24px",
              background: `rgba(74, 144, 217, ${0.1 + 0.15 * moldGlow})`,
              border: `2px solid ${COLORS.NOZZLE_BLUE}`,
              borderRadius: 8,
              boxShadow: `0 0 ${25 * moldGlow}px ${COLORS.NOZZLE_BLUE}`,
              fontSize: 14,
              fontWeight: "bold",
              color: COLORS.NOZZLE_BLUE,
            }}
          >
            PROMPT
          </div>

          {/* Tests */}
          <div
            style={{
              padding: "12px 24px",
              background: `rgba(217, 148, 74, ${0.1 + 0.15 * moldGlow})`,
              border: `2px solid ${COLORS.WALLS_AMBER}`,
              borderRadius: 8,
              boxShadow: `0 0 ${25 * moldGlow}px ${COLORS.WALLS_AMBER}`,
              fontSize: 14,
              fontWeight: "bold",
              color: COLORS.WALLS_AMBER,
            }}
          >
            TESTS
          </div>

          {/* Grounding */}
          <div
            style={{
              padding: "12px 24px",
              background: `rgba(90, 170, 110, ${0.1 + 0.15 * moldGlow})`,
              border: `2px solid ${COLORS.GROUNDING_GREEN}`,
              borderRadius: 8,
              boxShadow: `0 0 ${25 * moldGlow}px ${COLORS.GROUNDING_GREEN}`,
              fontSize: 14,
              fontWeight: "bold",
              color: COLORS.GROUNDING_GREEN,
            }}
          >
            GROUNDING
          </div>
        </div>

        {/* "The Mold" label */}
        <div
          style={{
            textAlign: "center",
            marginTop: 16,
            fontSize: 16,
            color: COLORS.LABEL_WHITE,
            opacity: moldGlow,
          }}
        >
          ═══ The Mold (Specification) ═══
        </div>
      </div>

      {/* Generated code */}
      <div
        style={{
          position: "absolute",
          bottom: 200,
          left: "50%",
          transform: "translateX(-50%)",
          opacity: codeOpacity,
        }}
      >
        <div
          style={{
            width: 500,
            padding: 20,
            background: "#1E1E2E",
            borderRadius: 8,
            boxShadow: codeGlow > 0.1
              ? `0 0 ${40 * codeGlow}px ${COLORS.CODE_GLOW}`
              : "none",
            border: codeGlow > 0.1
              ? `1px solid rgba(138, 156, 175, ${0.3 * codeGlow})`
              : "1px solid #333",
          }}
        >
          <pre
            style={{
              fontSize: 12,
              fontFamily: "JetBrains Mono, monospace",
              color: `rgba(160, 160, 160, ${0.5 + codeOpacity * 0.5})`,
              margin: 0,
              lineHeight: 1.5,
            }}
          >
            {GENERATED_CODE}
          </pre>
        </div>

        {/* "Output" label */}
        <div
          style={{
            textAlign: "center",
            marginTop: 12,
            fontSize: 14,
            color: COLORS.LABEL_GRAY,
            opacity: 1 - codeGlow * 0.5,
          }}
        >
          Generated Code (Output)
        </div>
      </div>

      {/* Final messages */}
      {showMessages && (
        <div
          style={{
            position: "absolute",
            bottom: 60,
            left: "50%",
            transform: "translateX(-50%)",
            textAlign: "center",
          }}
        >
          <div
            style={{
              fontSize: 32,
              color: COLORS.LABEL_GRAY,
              opacity: message1Opacity,
              marginBottom: 12,
            }}
          >
            The code is just plastic.
          </div>
          <div
            style={{
              fontSize: 36,
              color: COLORS.LABEL_WHITE,
              fontWeight: "bold",
              opacity: message2Opacity,
              textShadow: `0 0 20px ${COLORS.NOZZLE_BLUE}, 0 0 20px ${COLORS.WALLS_AMBER}, 0 0 20px ${COLORS.GROUNDING_GREEN}`,
            }}
          >
            The mold is what matters.
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
