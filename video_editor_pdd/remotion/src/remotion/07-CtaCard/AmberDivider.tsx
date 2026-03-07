import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  DIVIDER_EXPAND_START,
  DIVIDER_EXPAND_END,
  DIVIDER_MAX_WIDTH,
  DIVIDER_HEIGHT,
  DIVIDER_OPACITY,
  ACCENT_AMBER,
} from "./constants";

export const AmberDivider: React.FC = () => {
  const frame = useCurrentFrame();

  const width = interpolate(
    frame,
    [DIVIDER_EXPAND_START, DIVIDER_EXPAND_END],
    [0, DIVIDER_MAX_WIDTH],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
        marginTop: 4,
        marginBottom: 20,
        height: DIVIDER_HEIGHT + 8,
      }}
    >
      <div
        style={{
          width,
          height: DIVIDER_HEIGHT,
          backgroundColor: ACCENT_AMBER,
          opacity: DIVIDER_OPACITY,
          borderRadius: 1,
        }}
      />
    </div>
  );
};
