import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, TRADITIONAL_STEPS, PDD_STEPS, TraditionalVsPddPropsType } from "./constants";

/** Bug icon - red bug symbol */
const BugIcon: React.FC<{ size?: number; color?: string }> = ({ size = 24, color = "#E74C3C" }) => (
  <svg width={size} height={size} viewBox="0 0 24 24" fill="none">
    <path
      d="M12 2C10.9 2 10 2.9 10 4C10 4.7 10.4 5.3 11 5.6V7H9C7.9 7 7 7.9 7 9V11H5V13H7V15H5V17H7C7 19.2 8.8 21 11 21H13C15.2 21 17 19.2 17 17H19V15H17V13H19V11H17V9C17 7.9 16.1 7 15 7H13V5.6C13.6 5.3 14 4.7 14 4C14 2.9 13.1 2 12 2Z"
      fill={color}
    />
  </svg>
);

/** Band-aid icon - patch symbol */
const BandaidIcon: React.FC<{ size?: number; color?: string }> = ({ size = 24, color = "#E74C3C" }) => (
  <svg width={size} height={size} viewBox="0 0 24 24" fill="none">
    <rect x="3" y="10" width="18" height="4" rx="2" fill={color} opacity="0.3" />
    <rect x="10" y="3" width="4" height="18" rx="2" fill={color} opacity="0.3" />
    <circle cx="12" cy="12" r="3" fill={color} />
    <circle cx="8" cy="8" r="1.5" fill={color} opacity="0.6" />
    <circle cx="16" cy="8" r="1.5" fill={color} opacity="0.6" />
    <circle cx="8" cy="16" r="1.5" fill={color} opacity="0.6" />
    <circle cx="16" cy="16" r="1.5" fill={color} opacity="0.6" />
  </svg>
);

/** Wall icon - brick wall symbol */
const WallIcon: React.FC<{ size?: number; color?: string }> = ({ size = 24, color = "#D9944A" }) => (
  <svg width={size} height={size} viewBox="0 0 24 24" fill="none">
    <rect x="2" y="3" width="8" height="4" fill={color} stroke={color} strokeWidth="0.5" />
    <rect x="11" y="3" width="11" height="4" fill={color} stroke={color} strokeWidth="0.5" />
    <rect x="2" y="8" width="6" height="4" fill={color} stroke={color} strokeWidth="0.5" />
    <rect x="9" y="8" width="6" height="4" fill={color} stroke={color} strokeWidth="0.5" />
    <rect x="16" y="8" width="6" height="4" fill={color} stroke={color} strokeWidth="0.5" />
    <rect x="2" y="13" width="8" height="4" fill={color} stroke={color} strokeWidth="0.5" />
    <rect x="11" y="13" width="11" height="4" fill={color} stroke={color} strokeWidth="0.5" />
    <rect x="2" y="18" width="6" height="4" fill={color} stroke={color} strokeWidth="0.5" />
    <rect x="9" y="18" width="6" height="4" fill={color} stroke={color} strokeWidth="0.5" />
    <rect x="16" y="18" width="6" height="4" fill={color} stroke={color} strokeWidth="0.5" />
  </svg>
);

/** Regenerate icon - circular arrow */
const RegenerateIcon: React.FC<{ size?: number; color?: string }> = ({ size = 24, color = "#4CAF50" }) => (
  <svg width={size} height={size} viewBox="0 0 24 24" fill="none">
    <path
      d="M17.65 6.35C16.2 4.9 14.21 4 12 4c-4.42 0-7.99 3.58-7.99 8s3.57 8 7.99 8c3.73 0 6.84-2.55 7.73-6h-2.08c-.82 2.33-3.04 4-5.65 4-3.31 0-6-2.69-6-6s2.69-6 6-6c1.66 0 3.14.69 4.22 1.78L13 11h7V4l-2.35 2.35z"
      fill={color}
    />
  </svg>
);

/** Checkmark icon - success symbol */
const CheckmarkIcon: React.FC<{ size?: number; color?: string }> = ({ size = 24, color = "#4CAF50" }) => (
  <svg width={size} height={size} viewBox="0 0 24 24" fill="none">
    <circle cx="12" cy="12" r="10" fill={color} opacity="0.2" />
    <path
      d="M9 12l2 2 4-4"
      stroke={color}
      strokeWidth="2.5"
      strokeLinecap="round"
      strokeLinejoin="round"
      fill="none"
    />
  </svg>
);

/** Code block with bug - shows a snippet of code with a red bug highlight */
const CodeBlockWithBug: React.FC<{ opacity: number; hasBandaid?: boolean }> = ({ opacity, hasBandaid = false }) => (
  <div
    style={{
      position: "relative",
      background: "#1e1e2e",
      border: "1px solid #333",
      borderRadius: 4,
      padding: 8,
      fontSize: 11,
      fontFamily: "monospace",
      color: "#ccc",
      opacity,
      width: 200,
    }}
  >
    <div style={{ color: "#888" }}>{"// parse user input"}</div>
    <div style={{ background: hasBandaid ? "transparent" : "#E74C3C33", color: hasBandaid ? "#ccc" : "#E74C3C" }}>
      {"if (input.trim())"}
    </div>
    <div style={{ paddingLeft: 12 }}>{"  process(input)"}</div>
    {hasBandaid && (
      <div
        style={{
          position: "absolute",
          top: 18,
          left: 0,
          right: 0,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
        }}
      >
        <BandaidIcon size={40} color="#E74C3Caa" />
      </div>
    )}
  </div>
);

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
          <div style={{ position: "relative", width: 400, height: 500 }}>
            {/* Step 0: Write code */}
            {traditionalProgress >= 0 && (
              <div
                style={{
                  position: "absolute",
                  top: 0,
                  left: 0,
                  opacity: Math.min(1, Math.max(0, traditionalProgress - 0)),
                  display: "flex",
                  alignItems: "center",
                  gap: 12,
                }}
              >
                <div style={{ fontSize: 20 }}>{"📝"}</div>
                <span style={{ color: COLORS.LABEL_WHITE, fontSize: 16 }}>Write code</span>
              </div>
            )}

            {/* Step 1: Find bug - with code block */}
            {traditionalProgress >= 1 && (
              <div
                style={{
                  position: "absolute",
                  top: 50,
                  left: 0,
                  opacity: Math.min(1, Math.max(0, traditionalProgress - 1)),
                }}
              >
                <div style={{ display: "flex", alignItems: "center", gap: 12, marginBottom: 8 }}>
                  <BugIcon size={24} />
                  <span style={{ color: COLORS.LABEL_WHITE, fontSize: 16 }}>Find bug</span>
                </div>
                <CodeBlockWithBug opacity={1} />
              </div>
            )}

            {/* Step 2: Fix code - code with bandaid */}
            {traditionalProgress >= 2 && (
              <div
                style={{
                  position: "absolute",
                  top: 150,
                  left: 0,
                  opacity: Math.min(1, Math.max(0, traditionalProgress - 2)),
                }}
              >
                <div style={{ display: "flex", alignItems: "center", gap: 12, marginBottom: 8 }}>
                  <BandaidIcon size={24} />
                  <span style={{ color: COLORS.LABEL_WHITE, fontSize: 16 }}>Fix code</span>
                </div>
                <CodeBlockWithBug opacity={1} hasBandaid />
              </div>
            )}

            {/* Step 3: Find bug again */}
            {traditionalProgress >= 3 && (
              <div
                style={{
                  position: "absolute",
                  top: 250,
                  left: 0,
                  opacity: Math.min(1, Math.max(0, traditionalProgress - 3)),
                }}
              >
                <div style={{ display: "flex", alignItems: "center", gap: 12, marginBottom: 8 }}>
                  <BugIcon size={24} />
                  <span style={{ color: COLORS.LABEL_WHITE, fontSize: 16 }}>Find bug</span>
                </div>
                <CodeBlockWithBug opacity={1} />
              </div>
            )}

            {/* Step 4: Fix code again */}
            {traditionalProgress >= 4 && (
              <div
                style={{
                  position: "absolute",
                  top: 350,
                  left: 0,
                  opacity: Math.min(1, Math.max(0, traditionalProgress - 4)),
                }}
              >
                <div style={{ display: "flex", alignItems: "center", gap: 12, marginBottom: 8 }}>
                  <BandaidIcon size={24} />
                  <span style={{ color: COLORS.LABEL_WHITE, fontSize: 16 }}>Fix code</span>
                </div>
                <CodeBlockWithBug opacity={1} hasBandaid />
              </div>
            )}

            {/* Step 5: Find bug... (ellipsis indicating continuation) */}
            {traditionalProgress >= 5 && (
              <div
                style={{
                  position: "absolute",
                  top: 450,
                  left: 0,
                  opacity: Math.min(1, Math.max(0, traditionalProgress - 5)),
                  display: "flex",
                  alignItems: "center",
                  gap: 12,
                }}
              >
                <BugIcon size={24} />
                <span style={{ color: COLORS.LABEL_WHITE, fontSize: 16 }}>Find bug...</span>
              </div>
            )}

            {/* Cycle arrow with pulsing animation */}
            {traditionalProgress >= TRADITIONAL_STEPS.length && (
              <div
                style={{
                  position: "absolute",
                  top: 500,
                  left: "50%",
                  transform: "translateX(-50%)",
                  fontSize: 20,
                  color: COLORS.TRADITIONAL_RED,
                  opacity: 0.5 + 0.5 * Math.sin((frame / 30) * Math.PI * 2), // Pulsing effect
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
          <div style={{ position: "relative", width: 400, height: 500 }}>
            {/* Step 0: Define spec */}
            {pddProgress >= 0 && (
              <div
                style={{
                  position: "absolute",
                  top: 0,
                  left: 0,
                  opacity: Math.min(1, Math.max(0, pddProgress - 0)),
                  display: "flex",
                  alignItems: "center",
                  gap: 12,
                }}
              >
                <div style={{ fontSize: 20 }}>{"📋"}</div>
                <span style={{ color: COLORS.LABEL_WHITE, fontSize: 16 }}>Define spec (prompt + tests)</span>
              </div>
            )}

            {/* Step 1: Generate code */}
            {pddProgress >= 1 && (
              <div
                style={{
                  position: "absolute",
                  top: 70,
                  left: 0,
                  opacity: Math.min(1, Math.max(0, pddProgress - 1)),
                  display: "flex",
                  alignItems: "center",
                  gap: 12,
                }}
              >
                <RegenerateIcon size={24} color={COLORS.PDD_GREEN} />
                <span style={{ color: COLORS.LABEL_WHITE, fontSize: 16 }}>Generate code</span>
              </div>
            )}

            {/* Step 2: Bug found → add test with wall visualization */}
            {pddProgress >= 2 && (
              <div
                style={{
                  position: "absolute",
                  top: 140,
                  left: 0,
                  opacity: Math.min(1, Math.max(0, pddProgress - 2)),
                }}
              >
                <div style={{ display: "flex", alignItems: "center", gap: 12, marginBottom: 8 }}>
                  <BugIcon size={24} color="#E74C3C" />
                  <span style={{ color: COLORS.LABEL_WHITE, fontSize: 16 }}>Bug found → add test</span>
                </div>
                <div
                  style={{
                    display: "flex",
                    alignItems: "center",
                    gap: 8,
                    marginTop: 8,
                    padding: "8px 12px",
                    background: "#252535",
                    borderRadius: 4,
                    border: `1px solid ${COLORS.WALLS_AMBER}`,
                  }}
                >
                  <WallIcon size={32} color={COLORS.WALLS_AMBER} />
                  <div>
                    <div style={{ fontSize: 11, fontFamily: "monospace", color: "#4A90D9" }}>
                      $ pdd bug user_parser
                    </div>
                    <div style={{ fontSize: 10, color: COLORS.WALLS_AMBER, marginTop: 2 }}>
                      Wall materializes
                    </div>
                  </div>
                </div>
              </div>
            )}

            {/* Step 3: Regenerate code */}
            {pddProgress >= 3 && (
              <div
                style={{
                  position: "absolute",
                  top: 260,
                  left: 0,
                  opacity: Math.min(1, Math.max(0, pddProgress - 3)),
                }}
              >
                <div style={{ display: "flex", alignItems: "center", gap: 12, marginBottom: 8 }}>
                  <RegenerateIcon size={24} color={COLORS.PDD_GREEN} />
                  <span style={{ color: COLORS.LABEL_WHITE, fontSize: 16 }}>Regenerate code</span>
                </div>
                <div
                  style={{
                    padding: "8px 12px",
                    background: "#252535",
                    borderRadius: 4,
                    fontSize: 11,
                    fontFamily: "monospace",
                    color: "#4A90D9",
                    marginTop: 8,
                  }}
                >
                  $ pdd fix user_parser
                </div>
              </div>
            )}

            {/* Step 4: All tests pass - final checkmark */}
            {pddProgress >= 4 && (
              <div
                style={{
                  position: "absolute",
                  top: 360,
                  left: 0,
                  opacity: Math.min(1, Math.max(0, pddProgress - 4)),
                }}
              >
                <div
                  style={{
                    display: "flex",
                    alignItems: "center",
                    gap: 12,
                    padding: "12px 16px",
                    background: `${COLORS.PDD_GREEN}22`,
                    border: `2px solid ${COLORS.PDD_GREEN}`,
                    borderRadius: 8,
                  }}
                >
                  <CheckmarkIcon size={32} color={COLORS.PDD_GREEN} />
                  <div>
                    <div
                      style={{
                        color: COLORS.PDD_GREEN,
                        fontSize: 18,
                        fontWeight: "bold",
                      }}
                    >
                      All tests pass ✓
                    </div>
                    <div style={{ fontSize: 13, color: COLORS.LABEL_GRAY, marginTop: 2 }}>
                      Bug impossible forever
                    </div>
                  </div>
                </div>
              </div>
            )}
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
