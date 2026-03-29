import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  RATIO_COLOR,
  PROMPT_X,
  PROMPT_Y,
  PROMPT_WIDTH,
  PROMPT_HEIGHT,
  CODE_X,
  CODE_Y,
  CODE_HEIGHT,
  RATIO_ANIM_START,
  RATIO_ANIM_DUR,
} from "./constants";

export const RatioLabel: React.FC = () => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [RATIO_ANIM_START, RATIO_ANIM_START + RATIO_ANIM_DUR],
    [0, 1],
    {
      easing: Easing.out(Easing.back(1.4)),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const opacity = interpolate(
    frame,
    [RATIO_ANIM_START, RATIO_ANIM_START + RATIO_ANIM_DUR],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const scale = interpolate(progress, [0, 1], [0.8, 1]);

  // Position: centered between prompt and code blocks
  const labelX = (PROMPT_X + PROMPT_WIDTH + CODE_X) / 2;
  // Vertically: below prompt block, roughly aligned
  const labelY = PROMPT_Y + PROMPT_HEIGHT + 80;

  // Connector line endpoints
  const lineStartX = PROMPT_X + PROMPT_WIDTH;
  const lineEndX = CODE_X;
  const lineY = PROMPT_Y + PROMPT_HEIGHT / 2 + 20; // offset for label position
  const codeMidY = CODE_Y + CODE_HEIGHT / 2;

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: 0,
        width: "100%",
        height: "100%",
        opacity,
        pointerEvents: "none",
      }}
    >
      {/* Connector line */}
      <svg
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: "100%",
          height: "100%",
        }}
      >
        <line
          x1={lineStartX + 10}
          y1={lineY}
          x2={lineEndX - 10}
          y2={codeMidY}
          stroke={`rgba(217, 148, 74, 0.2)`}
          strokeWidth={2}
          strokeDasharray="6 4"
        />
      </svg>

      {/* Ratio text */}
      <div
        style={{
          position: "absolute",
          left: labelX - 100,
          top: labelY,
          width: 200,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 36,
          fontWeight: 700,
          color: RATIO_COLOR,
          transform: `scale(${scale})`,
          textShadow: `0 0 20px rgba(226, 232, 240, 0.3)`,
        }}
      >
        1:5 to 1:10
      </div>
    </div>
  );
};
