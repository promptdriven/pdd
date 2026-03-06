import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BAR_EXPAND_START,
  BAR_EXPAND_END,
  BAR_SEGMENT_STAGGER,
  CARD_FADE_OUT_START,
  CARD_FADE_OUT_END,
  BAR_Y,
  BAR_HEIGHT,
  BAR_SEGMENT_WIDTH_LEFT,
  BAR_SEGMENT_WIDTH_CENTER,
  BAR_SEGMENT_WIDTH_RIGHT,
  ACCENT_GREEN,
  ACCENT_GOLD,
  ACCENT_PURPLE,
} from "./constants";

const SEGMENTS = [
  { color: ACCENT_GREEN, width: BAR_SEGMENT_WIDTH_LEFT, delay: 0 },
  { color: ACCENT_GOLD, width: BAR_SEGMENT_WIDTH_CENTER, delay: BAR_SEGMENT_STAGGER },
  { color: ACCENT_PURPLE, width: BAR_SEGMENT_WIDTH_RIGHT, delay: BAR_SEGMENT_STAGGER * 2 },
];

export const TricolorBar: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeOut = interpolate(
    frame,
    [CARD_FADE_OUT_START, CARD_FADE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: BAR_Y,
        left: "50%",
        transform: "translateX(-50%)",
        display: "flex",
        flexDirection: "row",
        height: BAR_HEIGHT,
        opacity: fadeOut,
        overflow: "hidden",
      }}
    >
      {SEGMENTS.map((segment, i) => {
        const segStart = BAR_EXPAND_START + segment.delay;
        const segEnd = BAR_EXPAND_END;

        const segmentWidth = interpolate(
          frame,
          [segStart, segEnd],
          [0, segment.width],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.inOut(Easing.cubic),
          }
        );

        return (
          <div
            key={i}
            style={{
              width: segmentWidth,
              height: BAR_HEIGHT,
              backgroundColor: segment.color,
            }}
          />
        );
      })}
    </div>
  );
};

export default TricolorBar;
