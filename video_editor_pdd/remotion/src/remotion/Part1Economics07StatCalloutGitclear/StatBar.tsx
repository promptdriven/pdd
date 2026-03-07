import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BAR_TRACK_HEIGHT,
  BAR_TRACK_BG,
  BAR_TRACK_BORDER_RADIUS,
  LABEL_COLOR,
  LABEL_FONT_SIZE,
  STAT_FONT_SIZE,
  ARROW_SIZE,
  STAT_VALUE_COLOR,
} from "./constants";

interface StatBarProps {
  label: string;
  maxValue: number;
  prefix: string;
  suffix: string;
  fillTarget: number;
  gradient: readonly [string, string];
  direction: "up" | "down";
  animStart: number;
  animEnd: number;
}

export const StatBar: React.FC<StatBarProps> = ({
  label,
  maxValue,
  prefix,
  suffix,
  fillTarget,
  gradient,
  direction,
  animStart,
  animEnd,
}) => {
  const frame = useCurrentFrame();

  // Bar fill: easeOutQuart via supported quartic polynomial easing
  const fill = interpolate(frame, [animStart, animEnd], [0, fillTarget], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.poly(4)),
  });

  // Counter animate: easeOutCubic
  const value = Math.round(
    interpolate(frame, [animStart, animEnd], [0, maxValue], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    })
  );

  // Fade in the entire bar row
  const barOpacity = interpolate(frame, [animStart, animStart + 8], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Arrow pulse: oscillates briefly after bar fill completes
  const pulsePhase = frame - animEnd;
  const arrowScale =
    pulsePhase > 0 && pulsePhase < 30
      ? 1 + 0.15 * Math.sin((pulsePhase / 30) * Math.PI * 2)
      : 1;

  const arrow = direction === "up" ? "▲" : "▼";

  return (
    <div style={{ opacity: barOpacity, marginBottom: 24 }}>
      {/* Label + stat value row */}
      <div
        style={{
          display: "flex",
          justifyContent: "space-between",
          alignItems: "baseline",
          marginBottom: 10,
        }}
      >
        <span
          style={{
            fontFamily: "'Inter', sans-serif",
            fontWeight: 600,
            fontSize: LABEL_FONT_SIZE,
            color: LABEL_COLOR,
          }}
        >
          {label}
        </span>
        <div style={{ display: "flex", alignItems: "center", gap: 8 }}>
          <span
            style={{
              fontFamily: "'Inter', sans-serif",
              fontWeight: 900,
              fontSize: STAT_FONT_SIZE,
              color: STAT_VALUE_COLOR,
            }}
          >
            {prefix}
            {value}
            {suffix}
          </span>
          <span
            style={{
              fontSize: ARROW_SIZE,
              color: STAT_VALUE_COLOR,
              transform: `scale(${arrowScale})`,
              display: "inline-block",
            }}
          >
            {arrow}
          </span>
        </div>
      </div>

      {/* Bar track */}
      <div
        style={{
          width: "100%",
          height: BAR_TRACK_HEIGHT,
          backgroundColor: BAR_TRACK_BG,
          borderRadius: BAR_TRACK_BORDER_RADIUS,
          overflow: "hidden",
        }}
      >
        <div
          style={{
            width: `${fill * 100}%`,
            height: "100%",
            background: `linear-gradient(to right, ${gradient[0]}, ${gradient[1]})`,
            borderRadius: BAR_TRACK_BORDER_RADIUS,
          }}
        />
      </div>
    </div>
  );
};
