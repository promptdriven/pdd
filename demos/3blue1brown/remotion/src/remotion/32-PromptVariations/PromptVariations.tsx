import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, BASE_PROMPT, VARIATIONS, PromptVariationsPropsType } from "./constants";

export const PromptVariations: React.FC<PromptVariationsPropsType> = ({
  showVariations = true,
}) => {
  const frame = useCurrentFrame();

  // Prompt visibility
  const promptOpacity = interpolate(
    frame,
    [BEATS.PROMPT_START, BEATS.PROMPT_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Variation opacities
  const variation1Opacity = interpolate(
    frame,
    [BEATS.VARIATION_1_START, BEATS.VARIATION_1_START + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const variation2Opacity = interpolate(
    frame,
    [BEATS.VARIATION_2_START, BEATS.VARIATION_2_START + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const variation3Opacity = interpolate(
    frame,
    [BEATS.VARIATION_3_START, BEATS.VARIATION_3_START + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const variationOpacities = [variation1Opacity, variation2Opacity, variation3Opacity];

  // Insight
  const insightOpacity = interpolate(
    frame,
    [BEATS.INSIGHT_START, BEATS.INSIGHT_START + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Prompt at top */}
      <div
        style={{
          position: "absolute",
          top: 80,
          left: "50%",
          transform: "translateX(-50%)",
          opacity: promptOpacity,
        }}
      >
        <div
          style={{
            background: "rgba(74, 144, 217, 0.2)",
            border: `2px solid ${COLORS.NOZZLE_BLUE}`,
            borderRadius: 12,
            padding: "16px 32px",
            boxShadow: `0 0 20px rgba(74, 144, 217, 0.3)`,
          }}
        >
          <div
            style={{
              fontSize: 12,
              color: COLORS.NOZZLE_BLUE,
              marginBottom: 8,
            }}
          >
            SAME PROMPT
          </div>
          <div
            style={{
              fontSize: 20,
              color: COLORS.LABEL_WHITE,
              fontFamily: "sans-serif",
            }}
          >
            "{BASE_PROMPT}"
          </div>
        </div>

        {/* Arrows pointing down */}
        <div
          style={{
            display: "flex",
            justifyContent: "center",
            gap: 150,
            marginTop: 20,
          }}
        >
          {[0, 1, 2].map((i) => (
            <div
              key={i}
              style={{
                fontSize: 24,
                color: COLORS.NOZZLE_BLUE,
                opacity: variationOpacities[i],
              }}
            >
              ↓
            </div>
          ))}
        </div>
      </div>

      {/* Variation outputs */}
      {showVariations && (
        <div
          style={{
            position: "absolute",
            top: 280,
            left: "50%",
            transform: "translateX(-50%)",
            display: "flex",
            gap: 30,
          }}
        >
          {VARIATIONS.map((variation, i) => (
            <div
              key={i}
              style={{
                opacity: variationOpacities[i],
                width: 300,
              }}
            >
              <div
                style={{
                  fontSize: 14,
                  color: COLORS.LABEL_GRAY,
                  marginBottom: 8,
                  textAlign: "center",
                }}
              >
                {variation.label}
              </div>
              <div
                style={{
                  background: "#1E1E2E",
                  padding: 16,
                  borderRadius: 8,
                  border: "1px solid #333",
                }}
              >
                <pre
                  style={{
                    fontSize: 12,
                    fontFamily: "JetBrains Mono, monospace",
                    color: COLORS.CODE_GRAY,
                    margin: 0,
                    lineHeight: 1.5,
                    whiteSpace: "pre-wrap",
                  }}
                >
                  {variation.code}
                </pre>
              </div>
            </div>
          ))}
        </div>
      )}

      {/* Insight */}
      {insightOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 120,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: insightOpacity,
          }}
        >
          <div
            style={{
              fontSize: 24,
              color: COLORS.LABEL_WHITE,
              fontFamily: "sans-serif",
              marginBottom: 12,
            }}
          >
            Same prompt, different outputs
          </div>
          <div
            style={{
              fontSize: 18,
              color: COLORS.LABEL_GRAY,
              fontFamily: "sans-serif",
            }}
          >
            Without tests, which one is correct?
          </div>
        </div>
      )}

      {/* Question mark */}
      {insightOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 60,
            left: "50%",
            transform: "translateX(-50%)",
            fontSize: 48,
            color: COLORS.NOZZLE_BLUE,
            opacity: insightOpacity,
          }}
        >
          ?
        </div>
      )}
    </AbsoluteFill>
  );
};
