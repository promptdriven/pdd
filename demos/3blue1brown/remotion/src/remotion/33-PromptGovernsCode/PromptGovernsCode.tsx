import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, PROMPT_LINES, CODE_PREVIEW, PromptGovernsCodePropsType } from "./constants";

export const PromptGovernsCode: React.FC<PromptGovernsCodePropsType> = ({
  promptLineCount = 4,
  codeLineCount = 30,
}) => {
  const frame = useCurrentFrame();

  // Prompt visibility
  const promptOpacity = interpolate(
    frame,
    [BEATS.PROMPT_START, BEATS.PROMPT_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Arrow
  const arrowOpacity = interpolate(
    frame,
    [BEATS.ARROW_START, BEATS.ARROW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Code expansion
  const codeHeight = interpolate(
    frame,
    [BEATS.CODE_EXPAND_START, BEATS.CODE_EXPAND_END],
    [0, 400],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Ratio display
  const ratioOpacity = interpolate(
    frame,
    [BEATS.RATIO_START, BEATS.RATIO_START + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Insight
  const insightOpacity = interpolate(
    frame,
    [BEATS.INSIGHT_START, BEATS.INSIGHT_START + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      <div
        style={{
          display: "flex",
          width: "100%",
          height: "100%",
          padding: 60,
          gap: 40,
        }}
      >
        {/* Left side: Prompt */}
        <div
          style={{
            flex: 1,
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
            opacity: promptOpacity,
          }}
        >
          <div
            style={{
              fontSize: 20,
              color: COLORS.NOZZLE_BLUE,
              marginBottom: 20,
              fontWeight: "bold",
            }}
          >
            PROMPT
          </div>
          <div
            style={{
              background: "rgba(74, 144, 217, 0.15)",
              border: `2px solid ${COLORS.NOZZLE_BLUE}`,
              borderRadius: 12,
              padding: 24,
              width: "100%",
              maxWidth: 400,
            }}
          >
            {PROMPT_LINES.map((line, i) => (
              <div
                key={i}
                style={{
                  fontSize: 16,
                  color: COLORS.LABEL_WHITE,
                  marginBottom: i < PROMPT_LINES.length - 1 ? 12 : 0,
                  fontFamily: "sans-serif",
                  lineHeight: 1.5,
                }}
              >
                {line}
              </div>
            ))}
          </div>
          <div
            style={{
              marginTop: 16,
              fontSize: 14,
              color: COLORS.LABEL_GRAY,
            }}
          >
            ~{promptLineCount} lines
          </div>
        </div>

        {/* Arrow */}
        <div
          style={{
            display: "flex",
            alignItems: "center",
            opacity: arrowOpacity,
          }}
        >
          <div
            style={{
              fontSize: 48,
              color: COLORS.NOZZLE_BLUE,
            }}
          >
            →
          </div>
        </div>

        {/* Right side: Code */}
        <div
          style={{
            flex: 1.5,
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
            opacity: arrowOpacity,
          }}
        >
          <div
            style={{
              fontSize: 20,
              color: COLORS.CODE_GRAY,
              marginBottom: 20,
              fontWeight: "bold",
            }}
          >
            GENERATED CODE
          </div>
          <div
            style={{
              background: "#1E1E2E",
              border: "1px solid #333",
              borderRadius: 12,
              padding: 20,
              width: "100%",
              height: codeHeight,
              overflow: "hidden",
            }}
          >
            <pre
              style={{
                fontSize: 11,
                fontFamily: "JetBrains Mono, monospace",
                color: COLORS.CODE_GRAY,
                margin: 0,
                lineHeight: 1.4,
                whiteSpace: "pre-wrap",
              }}
            >
              {CODE_PREVIEW}
            </pre>
          </div>
          <div
            style={{
              marginTop: 16,
              fontSize: 14,
              color: COLORS.LABEL_GRAY,
            }}
          >
            ~{codeLineCount} lines
          </div>
        </div>
      </div>

      {/* Ratio display */}
      {ratioOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 140,
            left: "50%",
            transform: "translateX(-50%)",
            opacity: ratioOpacity,
          }}
        >
          <div
            style={{
              background: "rgba(255, 215, 0, 0.1)",
              border: `2px solid ${COLORS.RATIO_GOLD}`,
              borderRadius: 12,
              padding: "16px 40px",
            }}
          >
            <div
              style={{
                fontSize: 32,
                color: COLORS.RATIO_GOLD,
                fontWeight: "bold",
                textAlign: "center",
              }}
            >
              {promptLineCount} lines → {codeLineCount} lines
            </div>
            <div
              style={{
                fontSize: 16,
                color: COLORS.LABEL_GRAY,
                textAlign: "center",
                marginTop: 8,
              }}
            >
              {Math.round(codeLineCount / promptLineCount)}x amplification
            </div>
          </div>
        </div>
      )}

      {/* Insight */}
      {insightOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 50,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: insightOpacity,
          }}
        >
          <div
            style={{
              fontSize: 20,
              color: COLORS.LABEL_WHITE,
              fontFamily: "sans-serif",
            }}
          >
            The prompt governs what gets generated. Compact input, expanded output.
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
