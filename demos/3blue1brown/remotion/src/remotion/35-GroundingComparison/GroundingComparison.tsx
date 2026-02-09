import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, OOP_CODE, FUNCTIONAL_CODE, GroundingComparisonPropsType } from "./constants";

export const GroundingComparison: React.FC<GroundingComparisonPropsType> = ({
  showBothStyles = true,
}) => {
  const frame = useCurrentFrame();

  // Source visibility
  const sourceOpacity = interpolate(
    frame,
    [BEATS.SOURCE_START, BEATS.SOURCE_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Grounding labels
  const groundingOpacity = interpolate(
    frame,
    [BEATS.GROUNDING_START, BEATS.GROUNDING_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Code opacities
  const oopCodeOpacity = interpolate(
    frame,
    [BEATS.OOP_CODE_START, BEATS.OOP_CODE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  const funcCodeOpacity = interpolate(
    frame,
    [BEATS.FUNC_CODE_START, BEATS.FUNC_CODE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Checkmarks (with bounce effect)
  const checkmarkOpacity = interpolate(
    frame,
    [BEATS.CHECKMARKS_START, BEATS.CHECKMARKS_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.back(1.5)) }
  );

  // Insight
  const insightOpacity = interpolate(
    frame,
    [BEATS.INSIGHT_START, BEATS.INSIGHT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Shared source at top */}
      <div
        style={{
          position: "absolute",
          top: 40,
          left: "50%",
          transform: "translateX(-50%)",
          opacity: sourceOpacity,
          textAlign: "center",
        }}
      >
        <div style={{ fontSize: 16, color: COLORS.LABEL_GRAY, marginBottom: 12 }}>
          Same Prompt + Same Tests
        </div>
        <div style={{ display: "flex", gap: 20 }}>
          <div
            style={{
              padding: "8px 16px",
              background: "rgba(74, 144, 217, 0.2)",
              border: `1px solid ${COLORS.NOZZLE_BLUE}`,
              borderRadius: 6,
              fontSize: 12,
              color: COLORS.NOZZLE_BLUE,
            }}
          >
            PROMPT
          </div>
          <div
            style={{
              padding: "8px 16px",
              background: "rgba(217, 148, 74, 0.2)",
              border: `1px solid ${COLORS.WALLS_AMBER}`,
              borderRadius: 6,
              fontSize: 12,
              color: COLORS.WALLS_AMBER,
            }}
          >
            TESTS ████
          </div>
        </div>

        {/* Diverging arrows */}
        <div
          style={{
            marginTop: 20,
            fontSize: 24,
            color: COLORS.LABEL_GRAY,
          }}
        >
          ↙ ↘
        </div>
      </div>

      {/* Split comparison */}
      {showBothStyles && (
        <div
          style={{
            position: "absolute",
            top: 200,
            left: 0,
            right: 0,
            display: "flex",
            justifyContent: "center",
            gap: 40,
          }}
        >
          {/* OOP Path */}
          <div style={{ width: 420 }}>
            <div
              style={{
                fontSize: 14,
                color: COLORS.GROUNDING_GREEN,
                marginBottom: 12,
                opacity: groundingOpacity,
              }}
            >
              Grounding: OOP Codebase
            </div>
            <div
              style={{
                background: "#1E1E2E",
                padding: 16,
                borderRadius: 8,
                border: `1px solid ${COLORS.GROUNDING_GREEN}40`,
                opacity: oopCodeOpacity,
                boxShadow: `0 0 20px ${COLORS.GROUNDING_GREEN}20`,
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
                  filter: "hue-rotate(-10deg) saturate(1.2)",
                }}
              >
                {OOP_CODE}
              </pre>
            </div>
            {checkmarkOpacity > 0 && (
              <div
                style={{
                  marginTop: 12,
                  textAlign: "center",
                  fontSize: 20,
                  color: COLORS.SUCCESS_GREEN,
                  opacity: checkmarkOpacity,
                }}
              >
                ✓ All tests pass
              </div>
            )}
          </div>

          {/* Functional Path */}
          <div style={{ width: 420 }}>
            <div
              style={{
                fontSize: 14,
                color: COLORS.GROUNDING_GREEN,
                marginBottom: 12,
                opacity: groundingOpacity,
              }}
            >
              Grounding: Functional Codebase
            </div>
            <div
              style={{
                background: "#1E1E2E",
                padding: 16,
                borderRadius: 8,
                border: `1px solid ${COLORS.GROUNDING_GREEN}40`,
                opacity: funcCodeOpacity,
                boxShadow: `0 0 20px ${COLORS.GROUNDING_GREEN}20`,
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
                  filter: "hue-rotate(-10deg) saturate(1.2)",
                }}
              >
                {FUNCTIONAL_CODE}
              </pre>
            </div>
            {checkmarkOpacity > 0 && (
              <div
                style={{
                  marginTop: 12,
                  textAlign: "center",
                  fontSize: 20,
                  color: COLORS.SUCCESS_GREEN,
                  opacity: checkmarkOpacity,
                }}
              >
                ✓ All tests pass
              </div>
            )}
          </div>
        </div>
      )}

      {/* Insight */}
      {insightOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 80,
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
            Same behavior. Different style.
          </div>
          <div
            style={{
              fontSize: 18,
              color: COLORS.GROUNDING_GREEN,
              fontWeight: "bold",
            }}
          >
            Grounding determines HOW.
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
