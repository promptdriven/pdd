import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, TRADITIONAL_STEPS, PDD_STEPS, TraditionalVsPddPropsType } from "./constants";

/** Terminal snippet overlay for the PDD side, showing pdd bug and pdd fix commands. */
const PddTerminalOverlay: React.FC<{
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
        width: 300,
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
              fontSize: 12,
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

export const TraditionalVsPdd: React.FC<TraditionalVsPddPropsType> = ({
  showComparison = true,
}) => {
  const frame = useCurrentFrame();

  // Split screen appearance
  const splitOpacity = interpolate(
    frame,
    [BEATS.SPLIT_START, BEATS.SPLIT_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Traditional steps animation progress
  const traditionalProgress = interpolate(
    frame,
    [BEATS.TRADITIONAL_ANIMATE_START, BEATS.TRADITIONAL_ANIMATE_END],
    [0, TRADITIONAL_STEPS.length],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // PDD steps animation progress
  const pddProgress = interpolate(
    frame,
    [BEATS.PDD_ANIMATE_START, BEATS.PDD_ANIMATE_END],
    [0, PDD_STEPS.length],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Comparison highlight
  const comparisonOpacity = interpolate(
    frame,
    [BEATS.COMPARISON_START, BEATS.COMPARISON_START + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Insight text
  const insightOpacity = interpolate(
    frame,
    [BEATS.INSIGHT_START, BEATS.INSIGHT_START + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Terminal overlay opacity -- appears with PDD animation
  const terminalOpacity = interpolate(
    frame,
    [BEATS.PDD_ANIMATE_START + 30, BEATS.PDD_ANIMATE_START + 60],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Terminal lines (progressively revealed based on PDD flow)
  const terminalLines: Array<{ text: string; color?: string }> = [];
  if (frame >= BEATS.PDD_ANIMATE_START + 30) {
    terminalLines.push({ text: "$ pdd bug user_parser", color: "#4A90D9" });
  }
  if (pddProgress >= 2) {
    terminalLines.push({ text: "Test created: test_ws", color: "#ccc" });
  }
  if (pddProgress >= 3) {
    terminalLines.push({ text: "$ pdd fix user_parser", color: "#4A90D9" });
  }
  if (pddProgress >= 4) {
    terminalLines.push({ text: "All tests passing \u2713", color: "#4CAF50" });
  }

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Split screen container */}
      <div
        style={{
          display: "flex",
          width: "100%",
          height: "100%",
          opacity: splitOpacity,
        }}
      >
        {/* Traditional side (left) */}
        <div
          style={{
            flex: 1,
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
            padding: 60,
            borderRight: `2px solid ${COLORS.DIVIDER}`,
          }}
        >
          <div
            style={{
              fontSize: 28,
              fontWeight: "bold",
              color: COLORS.TRADITIONAL_RED,
              marginBottom: 40,
            }}
          >
            Traditional
          </div>

          {/* Cycle visualization */}
          <div style={{ position: "relative", width: 300, height: 400 }}>
            {TRADITIONAL_STEPS.map((step, i) => {
              const stepOpacity = Math.min(1, Math.max(0, traditionalProgress - i));
              const yOffset = i * 60;
              return (
                <div
                  key={i}
                  style={{
                    position: "absolute",
                    top: yOffset,
                    left: 0,
                    right: 0,
                    opacity: stepOpacity,
                    display: "flex",
                    alignItems: "center",
                    gap: 12,
                  }}
                >
                  <div
                    style={{
                      width: 24,
                      height: 24,
                      borderRadius: "50%",
                      background: i % 2 === 0 ? "rgba(231, 76, 60, 0.3)" : "rgba(231, 76, 60, 0.5)",
                      border: `2px solid ${COLORS.TRADITIONAL_RED}`,
                      display: "flex",
                      alignItems: "center",
                      justifyContent: "center",
                      fontSize: 12,
                      color: COLORS.TRADITIONAL_RED,
                    }}
                  >
                    {i + 1}
                  </div>
                  <span style={{ color: COLORS.LABEL_WHITE, fontSize: 16 }}>{step}</span>
                </div>
              );
            })}

            {/* Cycle arrow */}
            {traditionalProgress >= TRADITIONAL_STEPS.length && (
              <div
                style={{
                  position: "absolute",
                  top: TRADITIONAL_STEPS.length * 60 + 20,
                  left: "50%",
                  transform: "translateX(-50%)",
                  fontSize: 20,
                  color: COLORS.TRADITIONAL_RED,
                }}
              >
                {"\u21BB"} Repeat forever
              </div>
            )}
          </div>
        </div>

        {/* PDD side (right) */}
        <div
          style={{
            flex: 1,
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
            padding: 60,
            position: "relative",
          }}
        >
          <div
            style={{
              fontSize: 28,
              fontWeight: "bold",
              color: COLORS.PDD_GREEN,
              marginBottom: 40,
            }}
          >
            PDD
          </div>

          {/* Linear progression */}
          <div style={{ position: "relative", width: 350, height: 400 }}>
            {PDD_STEPS.map((step, i) => {
              const stepOpacity = Math.min(1, Math.max(0, pddProgress - i));
              const yOffset = i * 70;
              const isLast = i === PDD_STEPS.length - 1;
              return (
                <div
                  key={i}
                  style={{
                    position: "absolute",
                    top: yOffset,
                    left: 0,
                    right: 0,
                    opacity: stepOpacity,
                    display: "flex",
                    alignItems: "center",
                    gap: 12,
                  }}
                >
                  <div
                    style={{
                      width: 24,
                      height: 24,
                      borderRadius: "50%",
                      background: isLast ? COLORS.PDD_GREEN : "rgba(76, 175, 80, 0.3)",
                      border: `2px solid ${COLORS.PDD_GREEN}`,
                      display: "flex",
                      alignItems: "center",
                      justifyContent: "center",
                      fontSize: 12,
                      color: isLast ? "#fff" : COLORS.PDD_GREEN,
                    }}
                  >
                    {isLast ? "\u2713" : i + 1}
                  </div>
                  <span
                    style={{
                      color: isLast ? COLORS.PDD_GREEN : COLORS.LABEL_WHITE,
                      fontSize: 16,
                      fontWeight: isLast ? "bold" : "normal",
                    }}
                  >
                    {step}
                  </span>
                </div>
              );
            })}
          </div>

          {/* Terminal overlay inside PDD side */}
          <PddTerminalOverlay lines={terminalLines} opacity={terminalOpacity} />
        </div>
      </div>

      {/* Comparison highlight */}
      {showComparison && comparisonOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 150,
            left: 0,
            right: 0,
            display: "flex",
            justifyContent: "center",
            gap: 100,
            opacity: comparisonOpacity,
          }}
        >
          <div style={{ textAlign: "center" }}>
            <div style={{ fontSize: 36, color: COLORS.TRADITIONAL_RED }}>{"\u221E"}</div>
            <div style={{ fontSize: 14, color: COLORS.LABEL_GRAY }}>Endless cycle</div>
          </div>
          <div style={{ textAlign: "center" }}>
            <div style={{ fontSize: 36, color: COLORS.PDD_GREEN }}>{"\u2192"}</div>
            <div style={{ fontSize: 14, color: COLORS.LABEL_GRAY }}>Forward progress</div>
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
              fontSize: 22,
              color: COLORS.LABEL_WHITE,
              fontFamily: "sans-serif",
            }}
          >
            Traditional testing catches bugs. PDD testing{" "}
            <span style={{ color: COLORS.WALLS_AMBER, fontWeight: "bold" }}>prevents</span> them.
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
