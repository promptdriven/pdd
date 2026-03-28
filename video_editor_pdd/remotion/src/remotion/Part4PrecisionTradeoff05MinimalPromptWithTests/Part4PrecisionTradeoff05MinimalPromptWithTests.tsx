import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  WINDOW_FRAME_COLOR,
  TITLE_BAR_COLOR,
  FILENAME_COLOR,
  PROMPT_TEXT_COLOR,
  BLUE_ACCENT,
  GREEN_ACCENT,
  LABEL_COLOR,
  EDITOR_X,
  EDITOR_Y,
  EDITOR_WIDTH,
  EDITOR_HEIGHT,
  TERMINAL_X,
  TERMINAL_Y,
  TERMINAL_WIDTH,
  TERMINAL_HEIGHT,
  TITLE_BAR_HEIGHT,
  WINDOW_BORDER_RADIUS,
  EDITOR_FADE_DURATION,
  TERMINAL_FADE_DURATION,
  TYPEWRITER_CHAR_FRAMES,
  TEST_CASCADE_RATE,
  SUMMARY_FADE_DURATION,
  LABEL_FADE_DURATION,
  FADEOUT_START,
  FADEOUT_DURATION,
  PROMPT_FILENAME,
  PROMPT_LINE_COUNT,
  TEST_COUNT,
  TERMINAL_COMMAND,
  PROMPT_LINES,
  TEST_NAMES,
} from "./constants";
import { TestWalls } from "./TestWalls";

// ─── Default Props ───────────────────────────────────────────────────────────
export const defaultPart4PrecisionTradeoff05MinimalPromptWithTestsProps = {};

// ─── Sub-components ──────────────────────────────────────────────────────────

/** Editor window showing the compact prompt file */
const PromptEditor: React.FC<{ opacity: number }> = ({ opacity }) => {
  const frame = useCurrentFrame();

  // Lines appear during frames 0-30 (all visible once editor is in)
  const visibleLines = Math.min(
    PROMPT_LINES.length,
    Math.floor(
      interpolate(frame, [0, 30], [1, PROMPT_LINES.length], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
      })
    )
  );

  return (
    <div
      style={{
        position: "absolute",
        left: EDITOR_X,
        top: EDITOR_Y,
        width: EDITOR_WIDTH,
        height: EDITOR_HEIGHT,
        borderRadius: WINDOW_BORDER_RADIUS,
        border: `1px solid ${WINDOW_FRAME_COLOR}`,
        backgroundColor: WINDOW_FRAME_COLOR,
        overflow: "hidden",
        opacity,
        boxShadow: `0 0 12px rgba(74, 144, 217, 0.1)`,
      }}
    >
      {/* Title bar */}
      <div
        style={{
          height: TITLE_BAR_HEIGHT,
          backgroundColor: TITLE_BAR_COLOR,
          display: "flex",
          alignItems: "center",
          padding: "0 14px",
          gap: 12,
        }}
      >
        {/* Traffic lights */}
        <div style={{ display: "flex", gap: 6 }}>
          <div
            style={{
              width: 10,
              height: 10,
              borderRadius: "50%",
              backgroundColor: "#FF5F57",
            }}
          />
          <div
            style={{
              width: 10,
              height: 10,
              borderRadius: "50%",
              backgroundColor: "#FEBC2E",
            }}
          />
          <div
            style={{
              width: 10,
              height: 10,
              borderRadius: "50%",
              backgroundColor: "#28C840",
            }}
          />
        </div>

        {/* Filename */}
        <span
          style={{
            fontFamily: "JetBrains Mono, monospace",
            fontSize: 13,
            fontWeight: 400,
            color: FILENAME_COLOR,
          }}
        >
          {PROMPT_FILENAME}
        </span>

        {/* Line count badge */}
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 11,
            fontWeight: 600,
            color: BLUE_ACCENT,
            backgroundColor: "rgba(74, 144, 217, 0.15)",
            padding: "2px 8px",
            borderRadius: 4,
            marginLeft: "auto",
          }}
        >
          {PROMPT_LINE_COUNT} lines
        </span>
      </div>

      {/* Content area */}
      <div
        style={{
          padding: "12px 16px",
          overflow: "hidden",
        }}
      >
        {PROMPT_LINES.slice(0, visibleLines).map((line, i) => (
          <div
            key={i}
            style={{
              display: "flex",
              gap: 12,
              height: 20,
              alignItems: "center",
            }}
          >
            {/* Line number */}
            <span
              style={{
                fontFamily: "JetBrains Mono, monospace",
                fontSize: 12,
                color: "rgba(203, 213, 225, 0.3)",
                width: 20,
                textAlign: "right",
                flexShrink: 0,
              }}
            >
              {i + 1}
            </span>
            {/* Line content */}
            <span
              style={{
                fontFamily: "JetBrains Mono, monospace",
                fontSize: 13,
                fontWeight: 400,
                color:
                  line.startsWith("#")
                    ? BLUE_ACCENT
                    : PROMPT_TEXT_COLOR,
                whiteSpace: "nowrap",
                overflow: "hidden",
                textOverflow: "ellipsis",
              }}
            >
              {line}
            </span>
          </div>
        ))}
      </div>
    </div>
  );
};

/** Terminal window showing test run */
const TerminalWindow: React.FC<{ opacity: number }> = ({ opacity }) => {
  const frame = useCurrentFrame();

  // Typewriter effect for command (relative to terminal appear at frame 60)
  const termRelFrame = Math.max(0, frame - 60);
  const commandChars = Math.min(
    TERMINAL_COMMAND.length,
    Math.floor(termRelFrame / TYPEWRITER_CHAR_FRAMES)
  );
  const commandText = TERMINAL_COMMAND.slice(0, commandChars);

  // Test cascade starts at absolute frame 90
  const cascadeRelFrame = Math.max(0, frame - 90);
  const visibleTests = Math.min(
    TEST_COUNT,
    Math.floor(cascadeRelFrame * TEST_CASCADE_RATE)
  );

  // Summary appears at absolute frame 150
  const summaryOpacity = interpolate(
    frame,
    [150, 150 + SUMMARY_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Terminal pulse effect when tests are cascading
  const pulseIntensity =
    visibleTests > 0 && visibleTests < TEST_COUNT
      ? 0.03 * Math.sin(frame * 0.3)
      : 0;

  // How many tests to display (max visible rows)
  const maxVisibleRows = 18;
  const displayStart = Math.max(0, visibleTests - maxVisibleRows);
  const displayTests = TEST_NAMES.slice(displayStart, visibleTests);

  return (
    <div
      style={{
        position: "absolute",
        left: TERMINAL_X,
        top: TERMINAL_Y,
        width: TERMINAL_WIDTH,
        height: TERMINAL_HEIGHT,
        borderRadius: WINDOW_BORDER_RADIUS,
        border: `1px solid ${WINDOW_FRAME_COLOR}`,
        backgroundColor: WINDOW_FRAME_COLOR,
        overflow: "hidden",
        opacity,
        boxShadow: `0 0 ${8 + pulseIntensity * 100}px rgba(90, 170, 110, ${0.05 + pulseIntensity})`,
      }}
    >
      {/* Title bar */}
      <div
        style={{
          height: TITLE_BAR_HEIGHT,
          backgroundColor: TITLE_BAR_COLOR,
          display: "flex",
          alignItems: "center",
          padding: "0 14px",
          gap: 12,
        }}
      >
        {/* Traffic lights */}
        <div style={{ display: "flex", gap: 6 }}>
          <div
            style={{
              width: 10,
              height: 10,
              borderRadius: "50%",
              backgroundColor: "#FF5F57",
            }}
          />
          <div
            style={{
              width: 10,
              height: 10,
              borderRadius: "50%",
              backgroundColor: "#FEBC2E",
            }}
          />
          <div
            style={{
              width: 10,
              height: 10,
              borderRadius: "50%",
              backgroundColor: "#28C840",
            }}
          />
        </div>

        {/* Terminal icon */}
        <span
          style={{
            fontFamily: "JetBrains Mono, monospace",
            fontSize: 12,
            color: "rgba(226, 232, 240, 0.5)",
          }}
        >
          ▸ Terminal
        </span>
      </div>

      {/* Terminal content */}
      <div
        style={{
          padding: "10px 16px",
          overflow: "hidden",
          height: TERMINAL_HEIGHT - TITLE_BAR_HEIGHT - 20,
          display: "flex",
          flexDirection: "column",
        }}
      >
        {/* Command line */}
        <div
          style={{
            fontFamily: "JetBrains Mono, monospace",
            fontSize: 13,
            fontWeight: 400,
            color: GREEN_ACCENT,
            marginBottom: 8,
            minHeight: 20,
          }}
        >
          {commandText}
          {commandChars < TERMINAL_COMMAND.length && (
            <span
              style={{
                opacity: Math.sin(frame * 0.2) > 0 ? 1 : 0,
                color: GREEN_ACCENT,
              }}
            >
              ▌
            </span>
          )}
        </div>

        {/* Test results */}
        <div style={{ flex: 1, overflow: "hidden" }}>
          {displayTests.map((testName, i) => {
            const actualIndex = displayStart + i;
            return (
              <div
                key={actualIndex}
                style={{
                  fontFamily: "JetBrains Mono, monospace",
                  fontSize: 12,
                  fontWeight: 400,
                  color: GREEN_ACCENT,
                  opacity: 0.8,
                  height: 22,
                  display: "flex",
                  alignItems: "center",
                  gap: 8,
                }}
              >
                <span style={{ color: GREEN_ACCENT }}>✓</span>
                <span>{testName}</span>
              </div>
            );
          })}
        </div>

        {/* Summary */}
        <div
          style={{
            fontFamily: "JetBrains Mono, monospace",
            fontSize: 14,
            fontWeight: 700,
            color: GREEN_ACCENT,
            opacity: summaryOpacity,
            marginTop: 8,
            paddingTop: 8,
            borderTop: `1px solid rgba(90, 170, 110, 0.2)`,
          }}
        >
          {TEST_COUNT} tests passing
        </div>
      </div>
    </div>
  );
};

/** Comparison label on the right side */
const ComparisonLabel: React.FC<{ opacity: number }> = ({ opacity }) => {
  return (
    <div
      style={{
        position: "absolute",
        left: 1020,
        top: 400,
        width: 360,
        opacity,
      }}
    >
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 15,
          fontWeight: 400,
          color: LABEL_COLOR,
          opacity: 0.78,
          lineHeight: 1.6,
          textAlign: "center",
        }}
      >
        With tests: prompt specifies only intent
      </div>
    </div>
  );
};

// ─── Main Component ──────────────────────────────────────────────────────────

export const Part4PrecisionTradeoff05MinimalPromptWithTests: React.FC = () => {
  const frame = useCurrentFrame();

  // Editor fade-in: frames 0-30
  const editorOpacity = interpolate(
    frame,
    [0, EDITOR_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Terminal fade-in: frames 60-90
  const terminalOpacity = interpolate(
    frame,
    [60, 60 + TERMINAL_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Label fade-in: frames 165-185
  const labelOpacity = interpolate(
    frame,
    [165, 165 + LABEL_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Global fade-out: frames 210-240
  const fadeOut = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_START + FADEOUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        opacity: fadeOut,
      }}
    >
      {/* Prompt Editor — always visible from frame 0 */}
      <PromptEditor opacity={editorOpacity} />

      {/* Terminal Window — appears at frame 60 */}
      <TerminalWindow opacity={terminalOpacity} />

      {/* Test Walls — draw from frame 120 */}
      {frame >= 120 && <TestWalls />}

      {/* Comparison Label */}
      <ComparisonLabel opacity={labelOpacity} />
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff05MinimalPromptWithTests;
