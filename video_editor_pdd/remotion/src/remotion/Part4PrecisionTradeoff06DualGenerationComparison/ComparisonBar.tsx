import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

interface ComparisonBarProps {
  barY: number;
  totalWidth: number;
  leftSegmentWidth: number;
  rightSegmentWidth: number;
  leftColor: string;
  rightColor: string;
  label: string;
  labelColor: string;
  callout: string;
  calloutColor: string;
  animStart: number;
  animDuration: number;
}

const ComparisonBar: React.FC<ComparisonBarProps> = ({
  barY,
  totalWidth,
  leftSegmentWidth,
  rightSegmentWidth,
  leftColor,
  rightColor,
  label,
  labelColor,
  callout,
  calloutColor,
  animStart,
  animDuration,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [animStart, animStart + animDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const barLeft = (1920 - totalWidth) / 2;
  const segmentGap = 6;

  const currentLeftW = leftSegmentWidth * progress;
  const currentRightW = rightSegmentWidth * progress;

  return (
    <div
      style={{
        position: "absolute",
        left: barLeft,
        top: barY,
        width: totalWidth,
        height: 60,
        opacity: progress > 0 ? 1 : 0,
      }}
    >
      {/* Label above bar */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontWeight: 400,
          color: labelColor,
          textAlign: "center",
          marginBottom: 8,
          opacity: Math.min(1, progress * 2),
        }}
      >
        {label}
      </div>

      {/* Bar segments */}
      <div
        style={{
          display: "flex",
          alignItems: "center",
          height: 18,
          gap: segmentGap,
        }}
      >
        {/* Left segment (50 lines — amber) */}
        <div
          style={{
            width: currentLeftW,
            height: "100%",
            backgroundColor: leftColor,
            opacity: 0.3,
            borderRadius: 3,
          }}
        />

        {/* Right segment (10 lines — blue) */}
        <div
          style={{
            width: currentRightW,
            height: "100%",
            backgroundColor: rightColor,
            opacity: 0.3,
            borderRadius: 3,
          }}
        />

        {/* Callout */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 14,
            fontWeight: 700,
            color: calloutColor,
            marginLeft: 10,
            opacity: Math.min(1, Math.max(0, (progress - 0.5) * 2)),
            whiteSpace: "nowrap",
          }}
        >
          {callout}
        </div>
      </div>
    </div>
  );
};

export default ComparisonBar;
