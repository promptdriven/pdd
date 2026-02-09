import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, BUGGY_CODE, FAILING_TEST, BugDiscoveredPropsType } from "./constants";

export const BugDiscovered: React.FC<BugDiscoveredPropsType> = ({
  showOverlay = true,
}) => {
  const frame = useCurrentFrame();

  // Code visibility
  const codeOpacity = interpolate(
    frame,
    [BEATS.CODE_START, BEATS.CODE_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Scan line position
  const scanY = interpolate(
    frame,
    [BEATS.SCAN_START, BEATS.SCAN_END],
    [0, 300],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.linear }
  );

  // Bug highlight
  const bugHighlight = interpolate(
    frame,
    [BEATS.BUG_HIGHLIGHT_START, BEATS.BUG_HIGHLIGHT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Bug pulse effect
  const bugPulse = frame > BEATS.BUG_HIGHLIGHT_START
    ? Math.sin((frame - BEATS.BUG_HIGHLIGHT_START) * 0.15) * 0.1 + 1
    : 1;

  // Red flash intensity
  const redFlash = interpolate(
    frame,
    [BEATS.RED_FLASH_START, BEATS.RED_FLASH_START + 15, BEATS.RED_FLASH_END],
    [0, 1, 0.3],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Test failure panel
  const failureOpacity = interpolate(
    frame,
    [BEATS.TEST_FAILURE_START, BEATS.TEST_FAILURE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Explanation
  const explanationOpacity = interpolate(
    frame,
    [BEATS.EXPLANATION_START, BEATS.EXPLANATION_START + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Red flash overlay */}
      {redFlash > 0 && (
        <div
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            right: 0,
            bottom: 0,
            background: `rgba(231, 76, 60, ${0.2 * redFlash})`,
            pointerEvents: "none",
          }}
        />
      )}

      {/* Code block */}
      <div
        style={{
          position: "absolute",
          top: 120,
          left: "50%",
          transform: "translateX(-50%)",
          opacity: codeOpacity,
        }}
      >
        <div
          style={{
            background: "#1E1E2E",
            padding: 24,
            borderRadius: 12,
            border: bugHighlight > 0 ? `2px solid ${COLORS.BUG_RED}` : "1px solid #333",
            boxShadow: bugHighlight > 0 ? `0 0 ${30 * bugHighlight}px ${COLORS.BUG_RED}` : "none",
            position: "relative",
          }}
        >
          <pre
            style={{
              fontSize: 16,
              fontFamily: "JetBrains Mono, monospace",
              color: COLORS.CODE_GRAY,
              margin: 0,
              lineHeight: 1.6,
            }}
          >
            {BUGGY_CODE.split('\n').map((line, i) => (
              <div
                key={i}
                style={{
                  background: line.includes('BUG:') && bugHighlight > 0
                    ? `rgba(231, 76, 60, ${0.3 * bugHighlight})`
                    : "transparent",
                  padding: line.includes('BUG:') ? "2px 4px" : "0",
                  borderRadius: 4,
                }}
              >
                {line}
              </div>
            ))}
          </pre>

          {/* Scan line */}
          {frame >= BEATS.SCAN_START && frame < BEATS.SCAN_END && (
            <div
              style={{
                position: "absolute",
                left: 0,
                right: 0,
                top: scanY,
                height: 2,
                background: `linear-gradient(to bottom, transparent, ${COLORS.BUG_RED}, transparent)`,
                boxShadow: `0 0 10px ${COLORS.BUG_RED}`,
                pointerEvents: "none",
              }}
            />
          )}

          {/* BUG label */}
          {bugHighlight > 0 && (
            <div
              style={{
                position: "absolute",
                right: -120,
                top: 90,
                fontSize: 24,
                fontWeight: "bold",
                color: COLORS.BUG_RED,
                opacity: bugHighlight,
                transform: `scale(${bugPulse})`,
                padding: "8px 16px",
                background: "rgba(217, 74, 74, 0.2)",
                border: `2px solid ${COLORS.BUG_RED}`,
                borderRadius: 8,
                boxShadow: `0 0 20px rgba(217, 74, 74, 0.5)`,
              }}
            >
              BUG
            </div>
          )}
        </div>
      </div>

      {/* Test failure panel */}
      {failureOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 180,
            left: "50%",
            transform: "translateX(-50%)",
            opacity: failureOpacity,
          }}
        >
          <div
            style={{
              background: "rgba(231, 76, 60, 0.15)",
              border: `2px solid ${COLORS.BUG_RED}`,
              borderRadius: 12,
              padding: 24,
              textAlign: "center",
            }}
          >
            <div
              style={{
                fontSize: 20,
                color: COLORS.BUG_RED,
                fontWeight: "bold",
                marginBottom: 16,
              }}
            >
              ✗ TEST FAILED
            </div>
            <div
              style={{
                fontFamily: "JetBrains Mono, monospace",
                fontSize: 16,
                color: COLORS.LABEL_WHITE,
              }}
            >
              <div>Input: {FAILING_TEST.input}</div>
              <div style={{ marginTop: 8 }}>
                Expected: <span style={{ color: "#4CAF50" }}>{FAILING_TEST.expected}</span>
              </div>
              <div style={{ marginTop: 4 }}>
                Actual: <span style={{ color: COLORS.BUG_RED }}>{FAILING_TEST.actual}</span>
              </div>
            </div>
          </div>
        </div>
      )}

      {/* Explanation */}
      {explanationOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 60,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: explanationOpacity,
          }}
        >
          <div
            style={{
              fontSize: 22,
              color: COLORS.LABEL_WHITE,
              fontFamily: "sans-serif",
            }}
          >
            The test wall caught the defect. Time to fix the mold.
          </div>
        </div>
      )}

      {/* Section header */}
      <div
        style={{
          position: "absolute",
          top: 40,
          left: 0,
          right: 0,
          textAlign: "center",
          opacity: codeOpacity,
        }}
      >
        <span
          style={{
            fontSize: 24,
            fontFamily: "sans-serif",
            color: COLORS.BUG_RED,
            fontWeight: "bold",
          }}
        >
          Bug Discovered
        </span>
      </div>
    </AbsoluteFill>
  );
};
