import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from "remotion";

/**
 * OverflowIndicator — Red dashed line + count label shown when
 * code blocks overflow the context window.
 */

interface OverflowIndicatorProps {
  windowLeft: number;
  windowTop: number;
  windowWidth: number;
  windowHeight: number;
  overflowCount: number;
  color: string;
  appearFrame: number;
}

export const OverflowIndicator: React.FC<OverflowIndicatorProps> = ({
  windowLeft,
  windowTop,
  windowWidth,
  windowHeight,
  overflowCount,
  color,
  appearFrame,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [appearFrame, appearFrame + 20],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const lineY = windowTop + windowHeight;

  return (
    <AbsoluteFill style={{ opacity }}>
      {/* Red dashed line at bottom of window */}
      <svg
        style={{
          position: "absolute",
          left: windowLeft - 20,
          top: lineY - 1,
          width: windowWidth + 40,
          height: 3,
          overflow: "visible",
        }}
      >
        <line
          x1={0}
          y1={1.5}
          x2={windowWidth + 40}
          y2={1.5}
          stroke={color}
          strokeWidth={1.5}
          strokeDasharray="6 4"
        />
      </svg>

      {/* Red glow below */}
      <div
        style={{
          position: "absolute",
          left: windowLeft,
          top: lineY,
          width: windowWidth,
          height: 40,
          background: `linear-gradient(to bottom, ${color}1A, transparent)`,
        }}
      />

      {/* Overflow count label */}
      <div
        style={{
          position: "absolute",
          left: windowLeft,
          top: lineY + 12,
          width: windowWidth,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontWeight: 400,
          color,
        }}
      >
        {overflowCount} modules can&apos;t be seen
      </div>
    </AbsoluteFill>
  );
};
