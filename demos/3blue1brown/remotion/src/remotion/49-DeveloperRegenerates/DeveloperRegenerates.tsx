import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing, OffthreadVideo, staticFile } from "remotion";
import { COLORS, BEATS, DeveloperRegeneratesPropsType } from "./constants";

// ── Typewriter text helper ──────────────────────────────────────
const TypewriterText: React.FC<{
  text: string;
  progress: number;
  color: string;
}> = ({ text, progress, color }) => {
  const visibleChars = Math.floor(progress * text.length);
  const displayed = text.substring(0, visibleChars);
  const showCursor = progress < 1;

  return (
    <span style={{ color }}>
      {displayed}
      {showCursor && (
        <span
          style={{
            color: "rgba(255, 255, 255, 0.6)",
            animation: "none",
          }}
        >
          _
        </span>
      )}
    </span>
  );
};

// ── Terminal Title Bar ──────────────────────────────────────────
const TerminalTitleBar: React.FC = () => (
  <div
    style={{
      display: "flex",
      gap: 6,
      marginBottom: 16,
      paddingBottom: 12,
      borderBottom: "1px solid rgba(255, 255, 255, 0.08)",
    }}
  >
    <div
      style={{
        width: 10,
        height: 10,
        borderRadius: "50%",
        backgroundColor: "rgba(255, 95, 86, 0.7)",
      }}
    />
    <div
      style={{
        width: 10,
        height: 10,
        borderRadius: "50%",
        backgroundColor: "rgba(255, 189, 46, 0.7)",
      }}
    />
    <div
      style={{
        width: 10,
        height: 10,
        borderRadius: "50%",
        backgroundColor: "rgba(39, 201, 63, 0.7)",
      }}
    />
    <span
      style={{
        marginLeft: 12,
        fontSize: 11,
        color: "rgba(255, 255, 255, 0.3)",
      }}
    >
      terminal
    </span>
  </div>
);

// ── Bug display pseudocode (frames 0-60) ──────────────────────
const BUG_CODE_LINES = [
  { text: "def parse(tokens):", highlight: false },
  { text: "    for i in range(len(tokens)):", highlight: false },
  { text: "        node = tokens[i + 1]", highlight: true },
  { text: "    return tree", highlight: false },
];

// ── Main Component ──────────────────────────────────────────────
export const DeveloperRegenerates: React.FC<DeveloperRegeneratesPropsType> = () => {
  const frame = useCurrentFrame();

  // Terminal visibility
  const terminalOpacity = interpolate(
    frame,
    [BEATS.TERMINAL_FADE_START, BEATS.TERMINAL_FADE_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Initial bug display opacity (visible frames 0-60, fades out before commands)
  const bugDisplayOpacity = interpolate(
    frame,
    [0, 30, 60, 85],
    [0, 1, 1, 0],
    { extrapolateRight: "clamp", extrapolateLeft: "clamp" }
  );

  // Bug command typing progress
  const bugCmdProgress = interpolate(
    frame,
    [BEATS.BUG_CMD_START, BEATS.BUG_CMD_END],
    [0, 1],
    { extrapolateRight: "clamp" }
  );

  // Bug output opacity (spec: easeOutQuad)
  const bugOutputOpacity = interpolate(
    frame,
    [BEATS.BUG_OUTPUT_START, BEATS.BUG_OUTPUT_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Fix command typing progress
  const fixCmdProgress = interpolate(
    frame,
    [BEATS.FIX_CMD_START, BEATS.FIX_CMD_END],
    [0, 1],
    { extrapolateRight: "clamp" }
  );

  // Regenerating text opacity (spec: easeOutQuad)
  const regenOpacity = interpolate(
    frame,
    [BEATS.FIX_REGEN_START, BEATS.FIX_REGEN_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Generated output opacity (spec: easeOutQuad)
  const generatedOpacity = interpolate(
    frame,
    [BEATS.FIX_OUTPUT_START, BEATS.FIX_OUTPUT_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Test command typing progress
  const testCmdProgress = interpolate(
    frame,
    [BEATS.TEST_CMD_START, BEATS.TEST_CMD_END],
    [0, 1],
    { extrapolateRight: "clamp" }
  );

  // Test result opacity (spec: easeOutQuad)
  const testResultOpacity = interpolate(
    frame,
    [BEATS.TEST_OUTPUT_START, BEATS.TEST_OUTPUT_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Checkmark scale (pop effect with overshoot - spec: easeOutBack)
  const checkScale = interpolate(
    frame,
    [BEATS.CHECK_START, BEATS.CHECK_POP, BEATS.CHECK_SETTLE],
    [0, 1.2, 1.0],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.back(1.7)) }
  );

  const checkOpacity = interpolate(
    frame,
    [BEATS.CHECK_START, BEATS.CHECK_START + 10],
    [0, 1],
    { extrapolateRight: "clamp" }
  );

  const lineStyle: React.CSSProperties = {
    marginBottom: 6,
    lineHeight: 1.6,
  };

  const outputStyle: React.CSSProperties = {
    marginBottom: 8,
    marginLeft: 16,
    lineHeight: 1.5,
  };

  // Animated dots for "Regenerating..."
  const dotsCount = Math.floor((frame % 30) / 10); // Cycles through 0, 1, 2 every 30 frames
  const animatedDots = ".".repeat(Math.min(dotsCount + 1, 3));

  return (
    <AbsoluteFill>
      {/* Video base layer */}
      <OffthreadVideo
        loop
        src={staticFile("veo_developer_edit.mp4")}
        style={{ width: "100%", height: "100%" }}
      />

      {/* Terminal window */}
      <div
        style={{
          position: "absolute",
          right: 120,
          top: 180,
          width: 500,
          opacity: terminalOpacity,
          backgroundColor: COLORS.TERMINAL_BG,
          borderRadius: 12,
          border: `1px solid ${COLORS.TERMINAL_BORDER}`,
          padding: 24,
          fontFamily: "JetBrains Mono, monospace",
          fontSize: 14,
          backdropFilter: "blur(8px)",
        }}
      >
        <TerminalTitleBar />

        {/* Initial bug display: pseudocode with red-highlighted bug line (frames 0-60) */}
        {bugDisplayOpacity > 0 && (
          <div style={{ opacity: bugDisplayOpacity, marginBottom: 12 }}>
            {BUG_CODE_LINES.map((line, i) => (
              <div
                key={i}
                style={{
                  lineHeight: 1.6,
                  padding: "1px 4px",
                  borderRadius: 3,
                  backgroundColor: line.highlight
                    ? "rgba(255, 60, 60, 0.15)"
                    : "transparent",
                  borderLeft: line.highlight
                    ? "2px solid rgba(255, 80, 80, 0.8)"
                    : "2px solid transparent",
                }}
              >
                <span
                  style={{
                    color: line.highlight
                      ? "rgba(255, 100, 100, 0.9)"
                      : "rgba(255, 255, 255, 0.6)",
                    fontSize: 13,
                  }}
                >
                  {line.text}
                </span>
              </div>
            ))}
          </div>
        )}

        {/* Bug command */}
        <div style={lineStyle}>
          <span style={{ color: "rgba(255, 255, 255, 0.4)" }}>$ </span>
          <TypewriterText
            text="pdd bug parser"
            progress={bugCmdProgress}
            color={COLORS.BUG_AMBER}
          />
        </div>

        {/* Bug output */}
        {bugOutputOpacity > 0 && (
          <div style={{ ...outputStyle, opacity: bugOutputOpacity }}>
            <span style={{ color: COLORS.ERROR_RED }}>
              Bug identified: off-by-one in line 23
            </span>
          </div>
        )}

        {/* Fix command */}
        {frame >= BEATS.FIX_CMD_START && (
          <div style={lineStyle}>
            <span style={{ color: "rgba(255, 255, 255, 0.4)" }}>$ </span>
            <TypewriterText
              text="pdd fix parser"
              progress={fixCmdProgress}
              color={COLORS.FIX_BLUE}
            />
          </div>
        )}

        {/* Regenerating indicator with animated dots */}
        {regenOpacity > 0 && generatedOpacity === 0 && (
          <div style={{ ...outputStyle, opacity: regenOpacity }}>
            <span style={{ color: COLORS.TEXT_DIM }}>
              Regenerating{animatedDots}
            </span>
          </div>
        )}

        {/* Generated output */}
        {generatedOpacity > 0 && (
          <div style={{ ...outputStyle, opacity: generatedOpacity }}>
            <span style={{ color: COLORS.TEXT_NORMAL }}>
              Generated parser.py (247 lines)
            </span>
          </div>
        )}

        {/* Test command */}
        {frame >= BEATS.TEST_CMD_START && (
          <div style={lineStyle}>
            <span style={{ color: "rgba(255, 255, 255, 0.4)" }}>$ </span>
            <TypewriterText
              text="pdd test parser"
              progress={testCmdProgress}
              color={COLORS.TEST_GREEN}
            />
          </div>
        )}

        {/* Test result */}
        {testResultOpacity > 0 && (
          <div style={{ ...outputStyle, opacity: testResultOpacity }}>
            <span style={{ color: COLORS.TEST_GREEN }}>47 tests passed </span>
            <span
              style={{
                color: COLORS.TEST_GREEN,
                fontSize: 20,
                display: "inline-block",
                transform: `scale(${checkScale})`,
                opacity: checkOpacity,
              }}
            >
              ✓
            </span>
          </div>
        )}
      </div>
    </AbsoluteFill>
  );
};
