import React from "react";
import {
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { ArrowIcon } from "./ArrowIcon";
import {
  LABEL_COLOR,
  STAT_VALUE_COLOR,
  BAR_TRACK_BG,
  LABEL_FONT_SIZE,
  STAT_FONT_SIZE,
  BAR_TRACK_WIDTH,
  BAR_TRACK_HEIGHT,
  BAR_BORDER_RADIUS,
} from "./constants";

interface StatBarProps {
  label: string;
  targetValue: number;
  prefix: string;
  fillTarget: number;
  gradientStart: string;
  gradientEnd: string;
  arrowDirection: "up" | "down";
  barStart: number;
  barEnd: number;
  gradientId: string;
}

export const StatBar: React.FC<StatBarProps> = ({
  label,
  targetValue,
  prefix,
  fillTarget,
  gradientStart,
  gradientEnd,
  arrowDirection,
  barStart,
  barEnd,
  gradientId,
}) => {
  const frame = useCurrentFrame();

  // Bar fill animation with supported quartic polynomial easing
  const fillProgress = interpolate(
    frame,
    [barStart, barEnd],
    [0, fillTarget],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(4)),
    }
  );

  // Counter animation with easeOutCubic
  const counterRaw = interpolate(
    frame,
    [barStart, barEnd],
    [0, targetValue],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );
  const counterValue = Math.round(counterRaw);

  // Arrow pulse when bar is filling
  const arrowPulse =
    frame >= barStart && frame <= barEnd + 20
      ? 1 + 0.15 * Math.sin(((frame - barStart) / 10) * Math.PI * 2)
      : 1;

  const fillWidth = fillProgress * BAR_TRACK_WIDTH;

  return (
    <div style={{ marginBottom: 24 }}>
      {/* Label row */}
      <div
        style={{
          display: "flex",
          alignItems: "center",
          justifyContent: "space-between",
          marginBottom: 10,
        }}
      >
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 600,
            fontSize: LABEL_FONT_SIZE,
            color: LABEL_COLOR,
            lineHeight: 1,
          }}
        >
          {label}
        </div>
        <div
          style={{
            display: "flex",
            alignItems: "center",
            gap: 8,
          }}
        >
          <div
            style={{
              fontFamily: "Inter, sans-serif",
              fontWeight: 900,
              fontSize: STAT_FONT_SIZE,
              color: STAT_VALUE_COLOR,
              lineHeight: 1,
            }}
          >
            {prefix}
            {counterValue}%
          </div>
          <div style={{ transform: `scale(${arrowPulse})` }}>
            <ArrowIcon direction={arrowDirection} />
          </div>
        </div>
      </div>

      {/* Bar track */}
      <div
        style={{
          width: BAR_TRACK_WIDTH,
          height: BAR_TRACK_HEIGHT,
          backgroundColor: BAR_TRACK_BG,
          borderRadius: BAR_BORDER_RADIUS,
          overflow: "hidden",
          position: "relative",
        }}
      >
        {/* SVG for gradient bar fill */}
        <svg
          width={BAR_TRACK_WIDTH}
          height={BAR_TRACK_HEIGHT}
          style={{ position: "absolute", top: 0, left: 0 }}
        >
          <defs>
            <linearGradient id={gradientId} x1="0%" y1="0%" x2="100%" y2="0%">
              <stop offset="0%" stopColor={gradientStart} />
              <stop offset="100%" stopColor={gradientEnd} />
            </linearGradient>
          </defs>
          <rect
            x={0}
            y={0}
            width={fillWidth}
            height={BAR_TRACK_HEIGHT}
            rx={BAR_BORDER_RADIUS}
            ry={BAR_BORDER_RADIUS}
            fill={`url(#${gradientId})`}
          />
        </svg>
      </div>
    </div>
  );
};

export default StatBar;
