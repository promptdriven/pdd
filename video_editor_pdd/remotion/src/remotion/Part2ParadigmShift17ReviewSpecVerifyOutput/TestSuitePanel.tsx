import React from "react";
import { interpolate, Easing, spring } from "remotion";
import {
  PANEL_BG,
  TEXT_COLOR,
  GREEN_ACCENT,
  TEST_X,
  TEST_Y,
  TEST_WIDTH,
  PANEL_RADIUS,
  PANEL_PADDING,
  HEADER_FONT_SIZE,
  HEADER_LETTER_SPACING,
  TEST_NAME_SIZE,
  PASS_LABEL_SIZE,
  TEST_FADE_DURATION,
  TEST_ROW_STAGGER,
  TEST_RESULTS,
  MORPH_START,
  MORPH_DURATION,
} from "./constants";

interface TestSuitePanelProps {
  localFrame: number;
  globalFrame: number;
  fps: number;
}

/**
 * Checkmark with spring-based bounce entrance.
 */
const CheckMark: React.FC<{ visible: boolean; localFrame: number; delay: number; fps: number }> = ({
  visible,
  localFrame,
  delay,
  fps,
}) => {
  if (!visible) return null;

  const checkFrame = Math.max(0, localFrame - delay);
  const scale = spring({
    frame: checkFrame,
    fps,
    config: { damping: 8, stiffness: 150, mass: 0.5 },
  });

  return (
    <div
      style={{
        width: 20,
        height: 20,
        flexShrink: 0,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        transform: `scale(${scale})`,
      }}
    >
      <svg width={20} height={20} viewBox="0 0 20 20">
        <path
          d="M4 10.5L8 14.5L16 6.5"
          fill="none"
          stroke={GREEN_ACCENT}
          strokeWidth={2.5}
          strokeLinecap="round"
          strokeLinejoin="round"
        />
      </svg>
    </div>
  );
};

export const TestSuitePanel: React.FC<TestSuitePanelProps> = ({
  localFrame,
  globalFrame,
  fps,
}) => {
  // Panel fade-in
  const panelOpacity = interpolate(
    localFrame,
    [0, TEST_FADE_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Slide in from right
  const slideX = interpolate(
    localFrame,
    [0, TEST_FADE_DURATION],
    [40, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Morph glow effect
  const morphProgress =
    globalFrame >= MORPH_START
      ? interpolate(
          globalFrame,
          [MORPH_START, MORPH_START + MORPH_DURATION],
          [0, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
        )
      : 0;

  const morphGlowIntensity = morphProgress * 0.15;
  const morphBlurRadius = 20 + morphProgress * 10;

  const containerHeight = PANEL_PADDING * 2 + 28 + TEST_RESULTS.length * 48;

  return (
    <div
      style={{
        position: "absolute",
        left: TEST_X + slideX,
        top: TEST_Y,
        width: TEST_WIDTH,
        height: containerHeight,
        opacity: panelOpacity,
      }}
    >
      {/* Green glow during morph */}
      {morphProgress > 0 && (
        <div
          style={{
            position: "absolute",
            inset: -20,
            borderRadius: PANEL_RADIUS + 20,
            boxShadow: `0 0 ${morphBlurRadius}px ${Math.round(morphBlurRadius * 0.5)}px ${GREEN_ACCENT}`,
            opacity: morphGlowIntensity,
            pointerEvents: "none",
          }}
        />
      )}

      {/* Panel background */}
      <div
        style={{
          position: "relative",
          width: "100%",
          height: "100%",
          backgroundColor: PANEL_BG,
          borderRadius: PANEL_RADIUS,
          padding: PANEL_PADDING,
          boxSizing: "border-box",
          overflow: "hidden",
        }}
      >
        {/* Header */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: HEADER_FONT_SIZE,
            fontWeight: 700,
            color: GREEN_ACCENT,
            letterSpacing: HEADER_LETTER_SPACING,
            marginBottom: 16,
          }}
        >
          TEST SUITE
        </div>

        {/* Test rows */}
        {TEST_RESULTS.map((test, i) => {
          const rowDelay = TEST_FADE_DURATION + i * TEST_ROW_STAGGER;
          const rowVisible = localFrame >= rowDelay;

          const rowOpacity = rowVisible
            ? interpolate(
                localFrame,
                [rowDelay, rowDelay + 10],
                [0, 1],
                { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
              )
            : 0;

          return (
            <div
              key={test.name}
              style={{
                display: "flex",
                alignItems: "center",
                gap: 12,
                height: 40,
                marginBottom: 8,
                opacity: rowOpacity,
              }}
            >
              <CheckMark
                visible={rowVisible}
                localFrame={localFrame}
                delay={rowDelay}
                fps={fps}
              />

              <div
                style={{
                  flex: 1,
                  fontFamily: "'JetBrains Mono', monospace",
                  fontSize: TEST_NAME_SIZE,
                  fontWeight: 400,
                  color: TEXT_COLOR,
                }}
              >
                {test.name}
              </div>

              <div
                style={{
                  fontFamily: "'JetBrains Mono', monospace",
                  fontSize: PASS_LABEL_SIZE,
                  fontWeight: 700,
                  color: GREEN_ACCENT,
                }}
              >
                PASS
              </div>
            </div>
          );
        })}
      </div>
    </div>
  );
};

export default TestSuitePanel;
