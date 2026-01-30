import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, FOCUS_TEST, FocusSingleWallPropsType } from "./constants";

export const FocusSingleWall: React.FC<FocusSingleWallPropsType> = ({
  testInput = "null",
  testOutput = "None",
}) => {
  const frame = useCurrentFrame();

  // Wall visibility
  const wallOpacity = interpolate(
    frame,
    [BEATS.WALL_VISIBLE_START, BEATS.WALL_VISIBLE_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Zoom progress
  const zoomScale = interpolate(
    frame,
    [BEATS.ZOOM_START, BEATS.ZOOM_END],
    [1, 2.5],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  // Highlight glow
  const highlightGlow = interpolate(
    frame,
    [BEATS.HIGHLIGHT_START, BEATS.HIGHLIGHT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Explanation text
  const explanationOpacity = interpolate(
    frame,
    [BEATS.EXPLANATION_START, BEATS.EXPLANATION_START + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Zooming container */}
      <div
        style={{
          position: "absolute",
          top: "50%",
          left: "50%",
          transform: `translate(-50%, -50%) scale(${zoomScale})`,
          opacity: wallOpacity,
        }}
      >
        {/* Single wall section */}
        <div
          style={{
            width: 200,
            height: 300,
            background: `rgba(217, 148, 74, ${0.3 + 0.4 * highlightGlow})`,
            border: `3px solid ${COLORS.WALLS_AMBER}`,
            borderRadius: 8,
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
            justifyContent: "center",
            boxShadow: highlightGlow > 0
              ? `0 0 ${40 * highlightGlow}px ${COLORS.WALLS_AMBER}, inset 0 0 ${20 * highlightGlow}px rgba(217, 148, 74, 0.3)`
              : "none",
          }}
        >
          {/* Test label */}
          <div
            style={{
              fontSize: 24,
              fontFamily: "JetBrains Mono, monospace",
              color: COLORS.WALLS_AMBER,
              textAlign: "center",
              textShadow: `0 0 ${10 * highlightGlow}px ${COLORS.WALLS_AMBER}`,
            }}
          >
            <div style={{ marginBottom: 8 }}>{testInput}</div>
            <div style={{ fontSize: 28, color: COLORS.LABEL_WHITE }}>→</div>
            <div style={{ marginTop: 8 }}>{testOutput}</div>
          </div>
        </div>
      </div>

      {/* Explanation panel */}
      {explanationOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 120,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: explanationOpacity,
          }}
        >
          <div
            style={{
              display: "inline-block",
              background: "rgba(30, 30, 46, 0.9)",
              padding: "20px 40px",
              borderRadius: 12,
              border: `1px solid ${COLORS.WALLS_AMBER}`,
            }}
          >
            <div
              style={{
                fontSize: 22,
                color: COLORS.LABEL_WHITE,
                fontFamily: "sans-serif",
                marginBottom: 12,
              }}
            >
              {FOCUS_TEST.description}
            </div>
            <div
              style={{
                fontSize: 16,
                color: COLORS.LABEL_GRAY,
                fontFamily: "sans-serif",
              }}
            >
              This single test defines a constraint the code must satisfy.
            </div>
          </div>
        </div>
      )}

      {/* Section header */}
      <div
        style={{
          position: "absolute",
          top: 60,
          left: 0,
          right: 0,
          textAlign: "center",
          opacity: wallOpacity,
        }}
      >
        <span
          style={{
            fontSize: 20,
            fontFamily: "sans-serif",
            color: COLORS.WALLS_AMBER,
          }}
        >
          Focusing on a single constraint...
        </span>
      </div>
    </AbsoluteFill>
  );
};
