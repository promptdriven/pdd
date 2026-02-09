import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, BASE_PROMPT, VARIATIONS, PromptVariationsPropsType } from "./constants";

/** Terminal overlay styled as a small terminal window. */
const TerminalOverlay: React.FC<{
  lines: Array<{ text: string; color?: string }>;
  opacity: number;
}> = ({ lines, opacity }) => {
  if (opacity <= 0) return null;
  return (
    <div
      style={{
        position: "absolute",
        bottom: 30,
        right: 30,
        width: 400,
        opacity,
      }}
    >
      <div
        style={{
          background: "#252535",
          border: "1px solid #444",
          borderRadius: 6,
          padding: "10px 14px",
          minHeight: 80,
        }}
      >
        {/* Terminal title bar dots */}
        <div style={{ display: "flex", gap: 5, marginBottom: 8 }}>
          <div style={{ width: 8, height: 8, borderRadius: "50%", background: "#E74C3C" }} />
          <div style={{ width: 8, height: 8, borderRadius: "50%", background: "#F1C40F" }} />
          <div style={{ width: 8, height: 8, borderRadius: "50%", background: "#2ECC71" }} />
        </div>
        {lines.map((line, i) => (
          <div
            key={i}
            style={{
              fontSize: 11,
              fontFamily: "JetBrains Mono, monospace",
              color: line.color || "#ccc",
              lineHeight: 1.6,
              whiteSpace: "pre",
            }}
          >
            {line.text}
          </div>
        ))}
      </div>
    </div>
  );
};

/** Difference highlight box component */
const DifferenceHighlight: React.FC<{
  text: string;
  side: "left" | "right";
  line: number;
  opacity: number;
}> = ({ text, side, line, opacity }) => {
  if (opacity <= 0) return null;

  const leftOffset = side === "left" ? 490 : 970;
  const topOffset = 350 + (line * 22); // Adjust line spacing

  return (
    <div
      style={{
        position: "absolute",
        left: leftOffset,
        top: topOffset,
        padding: "2px 6px",
        background: "rgba(255, 170, 85, 0.25)",
        border: "1px solid #FFAA55",
        borderRadius: 4,
        opacity,
        fontSize: 11,
        color: "#FFAA55",
        fontFamily: "JetBrains Mono, monospace",
        pointerEvents: "none",
      }}
    >
      {text}
    </div>
  );
};

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

  const variationOpacities = [variation1Opacity, variation2Opacity];

  // Difference highlights
  const diffHighlightOpacity = interpolate(
    frame,
    [BEATS.DIFF_HIGHLIGHT_START, BEATS.DIFF_HIGHLIGHT_START + 30],
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

  // Checkmarks (separate timing for each)
  const checkmark1Opacity = interpolate(
    frame,
    [BEATS.VARIATION_1_START + 80, BEATS.VARIATION_1_START + 110],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const checkmark2Opacity = interpolate(
    frame,
    [BEATS.VARIATION_2_START + 80, BEATS.VARIATION_2_START + 110],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Terminal overlay
  const terminalOpacity = interpolate(
    frame,
    [BEATS.VARIATION_1_START, BEATS.VARIATION_1_START + 20],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Terminal lines based on frame
  const terminalLines: Array<{ text: string; color?: string }> = [];
  if (frame >= BEATS.VARIATION_1_START) {
    terminalLines.push({ text: "$ pdd generate user_parser.prompt", color: "#4A90D9" });
  }
  if (frame >= BEATS.VARIATION_1_START + 60) {
    terminalLines.push({ text: "Generated: parser_v1.py ✓", color: "#2ECC71" });
  }
  if (frame >= BEATS.VARIATION_2_START) {
    terminalLines.push({ text: "$ pdd generate user_parser.prompt", color: "#4A90D9" });
  }
  if (frame >= BEATS.VARIATION_2_START + 60) {
    terminalLines.push({ text: "Generated: parser_v2.py ✓", color: "#2ECC71" });
  }

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

        {/* Diverging arrows - SVG visualization */}
        <svg
          style={{
            position: "absolute",
            top: 60,
            left: -100,
            width: 200,
            height: 140,
            opacity: promptOpacity,
          }}
          viewBox="0 0 200 140"
        >
          {/* Center line down */}
          <path
            d="M 100 0 L 100 40"
            stroke={COLORS.NOZZLE_BLUE}
            strokeWidth="2"
            fill="none"
            opacity={promptOpacity}
          />
          {/* Left diverging arrow */}
          <path
            d="M 100 40 Q 100 70, 30 100 L 30 130"
            stroke={COLORS.NOZZLE_BLUE}
            strokeWidth="2"
            fill="none"
            opacity={variation1Opacity}
          />
          <path
            d="M 25 120 L 30 130 L 35 120"
            stroke={COLORS.NOZZLE_BLUE}
            strokeWidth="2"
            fill="none"
            opacity={variation1Opacity}
          />
          {/* Right diverging arrow */}
          <path
            d="M 100 40 Q 100 70, 170 100 L 170 130"
            stroke={COLORS.NOZZLE_BLUE}
            strokeWidth="2"
            fill="none"
            opacity={variation2Opacity}
          />
          <path
            d="M 165 120 L 170 130 L 175 120"
            stroke={COLORS.NOZZLE_BLUE}
            strokeWidth="2"
            fill="none"
            opacity={variation2Opacity}
          />
        </svg>
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
          {VARIATIONS.map((variation, i) => {
            const checkmarkOpacity = i === 0 ? checkmark1Opacity : checkmark2Opacity;
            return (
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
                    position: "relative",
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
                  {/* Individual checkmark for this variation */}
                  {checkmarkOpacity > 0 && (
                    <div
                      style={{
                        position: "absolute",
                        bottom: -35,
                        left: "50%",
                        transform: "translateX(-50%)",
                        fontSize: 16,
                        color: "#4CAF50",
                        opacity: checkmarkOpacity,
                        fontFamily: "sans-serif",
                      }}
                    >
                      ✓ Tests pass
                    </div>
                  )}
                </div>
              </div>
            );
          })}
        </div>
      )}

      {/* Difference highlights - highlighting key differences between versions */}
      {diffHighlightOpacity > 0 && (
        <>
          {/* Parameter name differences */}
          <DifferenceHighlight
            text="input_str"
            side="left"
            line={0}
            opacity={diffHighlightOpacity}
          />
          <DifferenceHighlight
            text="raw_input"
            side="right"
            line={0}
            opacity={diffHighlightOpacity}
          />
          {/* Variable name differences */}
          <DifferenceHighlight
            text="cleaned"
            side="left"
            line={3}
            opacity={diffHighlightOpacity}
          />
          <DifferenceHighlight
            text="sanitized"
            side="right"
            line={1}
            opacity={diffHighlightOpacity}
          />
        </>
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
              fontSize: 28,
              color: COLORS.LABEL_WHITE,
              fontFamily: "sans-serif",
              fontWeight: 600,
              textShadow: "0 2px 8px rgba(0,0,0,0.5)",
            }}
          >
            Code varies. Behavior is fixed.
          </div>
        </div>
      )}

      {/* Terminal overlay showing both generations */}
      <TerminalOverlay
        lines={terminalLines}
        opacity={terminalOpacity}
      />
    </AbsoluteFill>
  );
};
