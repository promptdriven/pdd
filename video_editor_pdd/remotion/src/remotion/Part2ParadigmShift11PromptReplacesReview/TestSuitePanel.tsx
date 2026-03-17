import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TEST_SUITE_START,
  CHECKMARK_INTERVAL,
  TEST_PANEL_X,
  TEST_PANEL_Y,
  TEST_PANEL_WIDTH,
  TEST_PANEL_HEIGHT,
  PANEL_BG,
  GREEN_ACCENT,
  TEST_ITEMS,
} from "./constants";

const CHECKMARK_POP_DURATION = 8;

interface TestLineProps {
  name: string;
  index: number;
}

const TestLine: React.FC<TestLineProps> = ({ name, index }) => {
  const frame = useCurrentFrame();
  const checkStartFrame = TEST_SUITE_START + index * CHECKMARK_INTERVAL;

  if (frame < checkStartFrame) {
    // Show the test name but no checkmark yet
    return (
      <div
        style={{
          fontFamily: "JetBrains Mono, monospace",
          fontSize: 11,
          lineHeight: "22px",
          color: GREEN_ACCENT,
          opacity: 0.2,
          display: "flex",
          alignItems: "center",
          gap: 8,
        }}
      >
        <span style={{ width: 16, display: "inline-block" }}>{"\u00A0"}</span>
        <span>{name}</span>
      </div>
    );
  }

  // Checkmark pop animation using easeOut(back(1.3)) approximation
  const localFrame = frame - checkStartFrame;
  const scaleRaw = interpolate(
    localFrame,
    [0, CHECKMARK_POP_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.back(1.3)),
    }
  );

  const checkOpacity = interpolate(
    localFrame,
    [0, CHECKMARK_POP_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        fontFamily: "JetBrains Mono, monospace",
        fontSize: 11,
        lineHeight: "22px",
        color: GREEN_ACCENT,
        opacity: 0.5,
        display: "flex",
        alignItems: "center",
        gap: 8,
      }}
    >
      <span
        style={{
          width: 16,
          display: "inline-block",
          transform: `scale(${scaleRaw})`,
          opacity: checkOpacity,
          color: GREEN_ACCENT,
          fontWeight: 700,
        }}
      >
        ✓
      </span>
      <span>{name}</span>
    </div>
  );
};

export const TestSuitePanel: React.FC = () => {
  const frame = useCurrentFrame();

  // Panel fades in at TEST_SUITE_START
  const panelOpacity = interpolate(
    frame,
    [TEST_SUITE_START, TEST_SUITE_START + 15],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  if (frame < TEST_SUITE_START) return null;

  return (
    <div
      style={{
        position: "absolute",
        left: TEST_PANEL_X - TEST_PANEL_WIDTH / 2,
        top: TEST_PANEL_Y - TEST_PANEL_HEIGHT / 2,
        width: TEST_PANEL_WIDTH,
        height: TEST_PANEL_HEIGHT,
        backgroundColor: PANEL_BG,
        opacity: panelOpacity * 0.2 + 0.8 * panelOpacity,
        borderRadius: 4,
        padding: 16,
        boxSizing: "border-box",
        overflow: "hidden",
      }}
    >
      {/* Header */}
      <div
        style={{
          fontFamily: "JetBrains Mono, monospace",
          fontSize: 10,
          color: GREEN_ACCENT,
          opacity: 0.4,
          marginBottom: 10,
        }}
      >
        test_suite.py
      </div>

      {/* Test lines */}
      {TEST_ITEMS.map((name, i) => (
        <TestLine key={name} name={name} index={i} />
      ))}
    </div>
  );
};
