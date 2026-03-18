import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  SUMMARY_START,
  SUMMARY_SLIDE_DURATION,
  SUMMARY_Y,
  PILL_PADDING,
  PILL_RADIUS,
  TEXT_COLOR,
  PATCHING_COLOR,
  PDD_COLOR,
} from "./constants";

export const SummaryLine: React.FC = () => {
  const frame = useCurrentFrame();
  const relFrame = frame - SUMMARY_START;

  if (relFrame < 0) return null;

  const slideY = interpolate(relFrame, [0, SUMMARY_SLIDE_DURATION], [20, 0], {
    easing: Easing.out(Easing.cubic),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const opacity = interpolate(relFrame, [0, SUMMARY_SLIDE_DURATION], [0, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div
      style={{
        position: "absolute",
        top: SUMMARY_Y,
        left: 0,
        right: 0,
        display: "flex",
        justifyContent: "center",
        transform: `translateY(${slideY}px)`,
        opacity,
      }}
    >
      <div
        style={{
          backgroundColor: `rgba(30, 41, 59, 0.25)`,
          borderRadius: PILL_RADIUS,
          padding: `${PILL_PADDING}px ${PILL_PADDING * 2}px`,
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 20,
            fontWeight: 600,
            lineHeight: 1.4,
          }}
        >
          <span style={{ color: TEXT_COLOR }}>One side compounds </span>
          <span style={{ color: PATCHING_COLOR }}>against you</span>
          <span style={{ color: TEXT_COLOR }}>. The other compounds </span>
          <span style={{ color: PDD_COLOR }}>for you</span>
          <span style={{ color: TEXT_COLOR }}>.</span>
        </span>
      </div>
    </div>
  );
};
