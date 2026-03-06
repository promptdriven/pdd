import React from "react";
import { useCurrentFrame, spring, interpolate, Easing } from "remotion";
import {
  BEFORE_ICON_MAP,
  AFTER_ICON_MAP,
  type BeforeIconType,
  type AfterIconType,
} from "./IndustryIcons";
import {
  COLUMN_WIDTH,
  BEFORE_ROW_Y,
  BEFORE_ROW_H,
  AFTER_ROW_Y,
  AFTER_ROW_H,
  BEFORE_COLOR,
  AFTER_COLOR,
  HEADER_COLOR,
  DESCRIPTOR_COLOR,
  ICON_SIZE,
  AFTER_ICON_SPRING,
  BEFORE_DIM_START,
  BEFORE_DIM_END,
  AFTER_REVEAL_START,
  FADEOUT_START,
  FADEOUT_END,
  FPS,
} from "./constants";

interface IndustryColumnProps {
  x: number;
  industry: string;
  beforeIcon: BeforeIconType;
  beforeText: string;
  afterIcon: AfterIconType;
  afterText: string;
  slideStart: number;
  slideEnd: number;
}

export const IndustryColumn: React.FC<IndustryColumnProps> = ({
  x,
  industry,
  beforeIcon,
  beforeText,
  afterIcon,
  afterText,
  slideStart,
  slideEnd,
}) => {
  const frame = useCurrentFrame();

  const slideX = interpolate(frame, [slideStart, slideEnd], [-100, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const columnOpacity = interpolate(
    frame,
    [slideStart, slideEnd, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const beforeDim = interpolate(
    frame,
    [BEFORE_DIM_START, BEFORE_DIM_END],
    [1.0, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const afterScale =
    frame >= AFTER_REVEAL_START
      ? spring({
          frame: frame - AFTER_REVEAL_START,
          fps: FPS,
          config: AFTER_ICON_SPRING,
        })
      : 0;

  const afterTextOpacity =
    frame >= AFTER_REVEAL_START
      ? interpolate(frame, [AFTER_REVEAL_START, AFTER_REVEAL_START + 30], [0, 1], {
          extrapolateRight: "clamp",
        })
      : 0;

  const BeforeIcon = BEFORE_ICON_MAP[beforeIcon];
  const AfterIcon = AFTER_ICON_MAP[afterIcon];

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: 0,
        width: COLUMN_WIDTH,
        height: "100%",
        transform: `translateX(${slideX}px)`,
        opacity: columnOpacity,
      }}
    >
      {/* Column header */}
      <div
        style={{
          position: "absolute",
          top: BEFORE_ROW_Y - 40,
          width: COLUMN_WIDTH,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontWeight: 700,
          fontSize: 18,
          color: HEADER_COLOR,
          letterSpacing: "0.12em",
          textTransform: "uppercase",
        }}
      >
        {industry}
      </div>

      {/* BEFORE row content */}
      <div
        style={{
          position: "absolute",
          top: BEFORE_ROW_Y,
          width: COLUMN_WIDTH,
          height: BEFORE_ROW_H,
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          justifyContent: "center",
          gap: 12,
          opacity: beforeDim,
        }}
      >
        <BeforeIcon size={ICON_SIZE} color={BEFORE_COLOR} />
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 500,
            fontSize: 16,
            color: DESCRIPTOR_COLOR,
          }}
        >
          {beforeText}
        </div>
      </div>

      {/* AFTER row content */}
      <div
        style={{
          position: "absolute",
          top: AFTER_ROW_Y,
          width: COLUMN_WIDTH,
          height: AFTER_ROW_H,
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          justifyContent: "center",
          gap: 12,
        }}
      >
        <div style={{ transform: `scale(${afterScale})` }}>
          <AfterIcon size={ICON_SIZE} color={AFTER_COLOR} />
        </div>
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 500,
            fontSize: 16,
            color: DESCRIPTOR_COLOR,
            opacity: afterTextOpacity,
          }}
        >
          {afterText}
        </div>
      </div>
    </div>
  );
};

export default IndustryColumn;
