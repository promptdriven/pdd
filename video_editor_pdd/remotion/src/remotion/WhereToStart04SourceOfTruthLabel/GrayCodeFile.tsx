import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  GRAY_FILE_X,
  GRAY_FILE_Y,
  GRAY_FILE_WIDTH,
  GRAY_FILE_HEIGHT,
  GRAY_FILE_OPACITY_START,
  GRAY_FILE_OPACITY_END,
  GRAY_FILE_NAME,
  TEXT_DIM,
  TEXT_MUTED,
  RECEDE_START,
  RECEDE_DURATION,
} from "./constants";

export const GrayCodeFile: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [RECEDE_START, RECEDE_START + RECEDE_DURATION],
    [GRAY_FILE_OPACITY_START, GRAY_FILE_OPACITY_END],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.ease) }
  );

  const scale = interpolate(
    frame,
    [RECEDE_START, RECEDE_START + RECEDE_DURATION],
    [1, 0.9],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.ease) }
  );

  const translateX = interpolate(
    frame,
    [RECEDE_START, RECEDE_START + RECEDE_DURATION],
    [0, -30],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.ease) }
  );

  // Fake code lines
  const codeLines = [
    { width: 120 },
    { width: 90 },
    { width: 150 },
    { width: 70 },
    { width: 130 },
    { width: 100 },
    { width: 80 },
    { width: 140 },
  ];

  return (
    <div
      style={{
        position: "absolute",
        left: GRAY_FILE_X - GRAY_FILE_WIDTH / 2,
        top: GRAY_FILE_Y - GRAY_FILE_HEIGHT / 2,
        width: GRAY_FILE_WIDTH,
        height: GRAY_FILE_HEIGHT,
        opacity,
        transform: `scale(${scale}) translateX(${translateX}px)`,
        borderRadius: 6,
        border: `1px solid ${TEXT_MUTED}`,
        backgroundColor: "#0D1117",
        overflow: "hidden",
      }}
    >
      {/* File header */}
      <div
        style={{
          padding: "6px 10px",
          borderBottom: `1px solid ${TEXT_MUTED}`,
          opacity: 0.3,
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 11,
            fontWeight: 500,
            color: TEXT_DIM,
            opacity: 0.3,
          }}
        >
          {GRAY_FILE_NAME}
        </span>
      </div>

      {/* Fake code lines */}
      <div style={{ padding: "8px 10px" }}>
        {codeLines.map((line, i) => (
          <div
            key={i}
            style={{
              width: line.width,
              height: 3,
              backgroundColor: TEXT_MUTED,
              opacity: 0.15,
              marginBottom: 5,
              borderRadius: 1.5,
            }}
          />
        ))}
      </div>
    </div>
  );
};
