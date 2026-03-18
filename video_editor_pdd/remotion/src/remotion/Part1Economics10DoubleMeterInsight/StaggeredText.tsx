import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface TextGroup {
  text: string;
  color: string;
}

interface StaggeredTextProps {
  groups: TextGroup[];
  startFrame: number;
  staggerDelay?: number;
  fadeDuration?: number;
  y: number;
}

const StaggeredText: React.FC<StaggeredTextProps> = ({
  groups,
  startFrame,
  staggerDelay = 10,
  fadeDuration = 15,
  y,
}) => {
  const frame = useCurrentFrame();

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: y,
        width: "100%",
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
        gap: 10,
      }}
    >
      {/* Subtle glow behind text */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: "50%",
          transform: "translate(-50%, -50%)",
          width: 500,
          height: 60,
          borderRadius: 30,
          background: `radial-gradient(ellipse, rgba(255,255,255,0.04), transparent 70%)`,
          filter: "blur(20px)",
          opacity: interpolate(
            frame,
            [startFrame, startFrame + fadeDuration],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          ),
          pointerEvents: "none",
        }}
      />

      {groups.map((group, i) => {
        const groupStart = startFrame + i * (fadeDuration + staggerDelay);
        const opacity = interpolate(
          frame,
          [groupStart, groupStart + fadeDuration],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          }
        );

        const translateY = interpolate(
          frame,
          [groupStart, groupStart + fadeDuration],
          [8, 0],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          }
        );

        return (
          <span
            key={i}
            style={{
              fontFamily: "Inter, sans-serif",
              fontSize: 22,
              fontWeight: 700,
              color: group.color,
              opacity: group.color === "#E2E8F0" ? opacity * 0.9 : opacity * 0.85,
              transform: `translateY(${translateY}px)`,
              whiteSpace: "nowrap",
            }}
          >
            {group.text}
          </span>
        );
      })}
    </div>
  );
};

export default StaggeredText;
