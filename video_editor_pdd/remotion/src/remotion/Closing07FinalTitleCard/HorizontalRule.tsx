import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  RULE_COLOR,
  RULE_OPACITY,
  RULE_WIDTH,
  RULE_DRAW_DURATION,
} from "./constants";

interface HorizontalRuleProps {
  y?: number;
  width?: number;
  color?: string;
  ruleOpacity?: number;
  drawFrames?: number;
}

export const HorizontalRule: React.FC<HorizontalRuleProps> = ({
  y = 0,
  width = RULE_WIDTH,
  color = RULE_COLOR,
  ruleOpacity = RULE_OPACITY,
  drawFrames = RULE_DRAW_DURATION,
}) => {
  const frame = useCurrentFrame();

  const widthProgress = interpolate(frame, [0, drawFrames], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  const currentWidth = width * widthProgress;

  return (
    <div
      style={{
        position: "absolute",
        top: y,
        left: 0,
        right: 0,
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
      }}
    >
      <div
        style={{
          width: currentWidth,
          height: 2,
          backgroundColor: color,
          opacity: ruleOpacity,
        }}
      />
    </div>
  );
};
