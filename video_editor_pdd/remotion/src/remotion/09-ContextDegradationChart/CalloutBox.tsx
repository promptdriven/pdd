import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, spring } from "remotion";
import {
  CHART_Y,
  CHART_H,
  CALLOUT_COLOR,
  CALLOUT_SOURCE_COLOR,
} from "./constants";

interface CalloutBoxProps {
  startFrame: number;
}

export const CalloutBox: React.FC<CalloutBoxProps> = ({ startFrame }) => {
  const frame = useCurrentFrame();

  const localFrame = frame - startFrame;
  if (localFrame < 0) return null;

  // Slide up + fade in with spring
  const slideProgress = spring({
    frame: localFrame,
    fps: 30,
    config: { damping: 15, stiffness: 180 },
  });

  const translateY = interpolate(slideProgress, [0, 1], [40, 0]);
  const opacity = interpolate(slideProgress, [0, 1], [0, 1]);

  // Positioned below chart area
  const boxTop = CHART_Y + CHART_H + 90;

  return (
    <AbsoluteFill>
      <div
        style={{
          position: "absolute",
          top: boxTop,
          left: 0,
          right: 0,
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          transform: `translateY(${translateY}px)`,
          opacity,
        }}
      >
        {/* Callout container */}
        <div
          style={{
            display: "flex",
            alignItems: "center",
            gap: 16,
            padding: "12px 32px",
            borderRadius: 8,
            border: `2px solid ${CALLOUT_COLOR}`,
            backgroundColor: "rgba(239, 68, 68, 0.1)",
          }}
        >
          {/* Red accent bar */}
          <div
            style={{
              width: 4,
              height: 40,
              backgroundColor: CALLOUT_COLOR,
              borderRadius: 2,
            }}
          />

          {/* Text */}
          <div style={{ display: "flex", flexDirection: "column", gap: 4 }}>
            <span
              style={{
                fontFamily: "Inter, sans-serif",
                fontWeight: 700,
                fontSize: 32,
                color: CALLOUT_COLOR,
                lineHeight: 1.2,
              }}
            >
              14-85% capability loss
            </span>
            <span
              style={{
                fontFamily: "Inter, sans-serif",
                fontWeight: 400,
                fontSize: 16,
                color: CALLOUT_SOURCE_COLOR,
                lineHeight: 1.2,
              }}
            >
              EMNLP 2024
            </span>
          </div>
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default CalloutBox;
