import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  VALUE_BAR_X,
  VALUE_BAR_Y,
  VALUE_BAR_HEIGHT,
  VALUE_BAR_WIDTH,
  VALUE_BAR_TRACK_COLOR,
  VALUE_BAR_GRADIENT_START,
  VALUE_BAR_GRADIENT_END,
  VALUE_BAR_INITIAL_PERCENT,
  VALUE_BAR_FINAL_PERCENT,
  VALUE_BAR_ANIM_START,
  VALUE_BAR_ANIM_END,
  PANEL_FADE_IN_START,
  PANEL_FADE_IN_END,
  FADEOUT_START,
  FADEOUT_END,
  LABEL_OBJECT_COLOR,
  LABEL_SPEC_COLOR,
  TEXT_WHITE,
} from "./constants";

export const ValueBar: React.FC = () => {
  const frame = useCurrentFrame();

  const appearOpacity = interpolate(
    frame,
    [PANEL_FADE_IN_START, PANEL_FADE_IN_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const fadeOutOpacity = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const opacity = appearOpacity * fadeOutOpacity;

  const fillPercent = interpolate(
    frame,
    [VALUE_BAR_ANIM_START, VALUE_BAR_ANIM_END],
    [VALUE_BAR_INITIAL_PERCENT, VALUE_BAR_FINAL_PERCENT],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const fillHeight = (fillPercent / 100) * VALUE_BAR_HEIGHT;
  const barTop = VALUE_BAR_Y;
  const barBottom = VALUE_BAR_Y + VALUE_BAR_HEIGHT;

  return (
    <AbsoluteFill style={{ opacity }}>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <linearGradient id="valueBarGrad" x1="0" y1="1" x2="0" y2="0">
            <stop offset="0%" stopColor={VALUE_BAR_GRADIENT_START} />
            <stop offset="100%" stopColor={VALUE_BAR_GRADIENT_END} />
          </linearGradient>
        </defs>

        {/* Track background */}
        <rect
          x={VALUE_BAR_X - VALUE_BAR_WIDTH / 2}
          y={barTop}
          width={VALUE_BAR_WIDTH}
          height={VALUE_BAR_HEIGHT}
          rx={VALUE_BAR_WIDTH / 2}
          fill={VALUE_BAR_TRACK_COLOR}
        />

        {/* Animated fill — grows from bottom */}
        <rect
          x={VALUE_BAR_X - VALUE_BAR_WIDTH / 2}
          y={barBottom - fillHeight}
          width={VALUE_BAR_WIDTH}
          height={fillHeight}
          rx={VALUE_BAR_WIDTH / 2}
          fill="url(#valueBarGrad)"
        />

        {/* Bottom label: "Object" */}
        <text
          x={VALUE_BAR_X}
          y={barBottom + 24}
          fill={LABEL_OBJECT_COLOR}
          fontSize={14}
          fontFamily="Inter, sans-serif"
          fontWeight={500}
          textAnchor="middle"
        >
          Object
        </text>

        {/* Top label: "Specification" */}
        <text
          x={VALUE_BAR_X}
          y={barTop - 30}
          fill={LABEL_SPEC_COLOR}
          fontSize={14}
          fontFamily="Inter, sans-serif"
          fontWeight={500}
          textAnchor="middle"
        >
          Specification
        </text>

        {/* Percentage readout */}
        <text
          x={VALUE_BAR_X}
          y={barTop - 54}
          fill={TEXT_WHITE}
          fontSize={28}
          fontFamily="JetBrains Mono, monospace"
          fontWeight={700}
          textAnchor="middle"
        >
          {`${Math.round(fillPercent)}%`}
        </text>
      </svg>
    </AbsoluteFill>
  );
};

export default ValueBar;
