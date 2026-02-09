import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, TEST_LABELS, WallsIlluminatePropsType } from "./constants";

export const WallsIlluminate: React.FC<WallsIlluminatePropsType> = ({
  showLabels = true,
}) => {
  const frame = useCurrentFrame();

  // Mold visibility
  const moldOpacity = interpolate(
    frame,
    [BEATS.MOLD_VISIBLE_START, BEATS.MOLD_VISIBLE_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Walls glow intensity
  const wallsGlow = interpolate(
    frame,
    [BEATS.WALLS_GLOW_START, BEATS.WALLS_GLOW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Mold dimensions
  const moldConfig = {
    centerX: 960,
    centerY: 540,
    width: 700,
    height: 500,
    wallThickness: 60,
  };

  // Individual wall pulse calculations
  const getWallPulse = (wallPosition: "top" | "right" | "bottom" | "left") => {
    const label = TEST_LABELS.find((l) => l.position === wallPosition);
    if (!label) return 0;

    return interpolate(
      frame,
      [label.start, label.start + 15, label.start + 30],
      [0, 0.3, 0],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.sine) }
    );
  };

  const topPulse = getWallPulse("top");
  const rightPulse = getWallPulse("right");
  const bottomPulse = getWallPulse("bottom");
  const leftPulse = getWallPulse("left");

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      <svg width="100%" height="100%" viewBox="0 0 1920 1080" style={{ opacity: moldOpacity }}>
        {/* Mold outline */}
        <rect
          x={moldConfig.centerX - moldConfig.width / 2}
          y={moldConfig.centerY - moldConfig.height / 2}
          width={moldConfig.width}
          height={moldConfig.height}
          fill="none"
          stroke={COLORS.OUTLINE_GRAY}
          strokeWidth={2}
          rx={8}
        />

        {/* Left wall with glow */}
        <rect
          x={moldConfig.centerX - moldConfig.width / 2}
          y={moldConfig.centerY - moldConfig.height / 2}
          width={moldConfig.wallThickness}
          height={moldConfig.height}
          fill={`rgba(217, 148, 74, ${0.2 + 0.5 * wallsGlow + leftPulse})`}
          stroke={COLORS.WALLS_AMBER}
          strokeWidth={2}
          style={{
            filter: `drop-shadow(0 0 ${30 * wallsGlow + 30 * leftPulse}px ${COLORS.WALLS_AMBER})`,
          }}
        />

        {/* Right wall with glow */}
        <rect
          x={moldConfig.centerX + moldConfig.width / 2 - moldConfig.wallThickness}
          y={moldConfig.centerY - moldConfig.height / 2}
          width={moldConfig.wallThickness}
          height={moldConfig.height}
          fill={`rgba(217, 148, 74, ${0.2 + 0.5 * wallsGlow + rightPulse})`}
          stroke={COLORS.WALLS_AMBER}
          strokeWidth={2}
          style={{
            filter: `drop-shadow(0 0 ${30 * wallsGlow + 30 * rightPulse}px ${COLORS.WALLS_AMBER})`,
          }}
        />

        {/* Bottom wall with glow */}
        <rect
          x={moldConfig.centerX - moldConfig.width / 2 + moldConfig.wallThickness}
          y={moldConfig.centerY + moldConfig.height / 2 - moldConfig.wallThickness}
          width={moldConfig.width - 2 * moldConfig.wallThickness}
          height={moldConfig.wallThickness}
          fill={`rgba(217, 148, 74, ${0.2 + 0.5 * wallsGlow + bottomPulse})`}
          stroke={COLORS.WALLS_AMBER}
          strokeWidth={2}
          style={{
            filter: `drop-shadow(0 0 ${30 * wallsGlow + 30 * bottomPulse}px ${COLORS.WALLS_AMBER})`,
          }}
        />

        {/* Top wall with glow */}
        <rect
          x={moldConfig.centerX - moldConfig.width / 2 + moldConfig.wallThickness}
          y={moldConfig.centerY - moldConfig.height / 2}
          width={moldConfig.width - 2 * moldConfig.wallThickness}
          height={moldConfig.wallThickness}
          fill={`rgba(217, 148, 74, ${0.2 + 0.5 * wallsGlow + topPulse})`}
          stroke={COLORS.WALLS_AMBER}
          strokeWidth={2}
          style={{
            filter: `drop-shadow(0 0 ${30 * wallsGlow + 30 * topPulse}px ${COLORS.WALLS_AMBER})`,
          }}
        />
      </svg>

      {/* Test labels on walls - one per wall */}
      {showLabels && (
        <div style={{ opacity: moldOpacity }}>
          {TEST_LABELS.map((label, i) => {
            // Label fade in
            const labelOpacity = interpolate(
              frame,
              [label.start, label.start + 30],
              [0, 1],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
            );

            // Wall pulse effect when label appears
            const wallPulse = interpolate(
              frame,
              [label.start, label.start + 15, label.start + 30],
              [0, 1, 0],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.sine) }
            );

            // Position based on wall
            let labelStyle: React.CSSProperties = {
              position: "absolute",
              fontSize: 24,
              fontFamily: "JetBrains Mono, monospace",
              color: "#FFF8F0",
              opacity: labelOpacity,
              textShadow: `0 2px 4px rgba(0, 0, 0, 0.5), 0 0 ${10 + 10 * wallPulse}px ${COLORS.WALLS_AMBER}`,
            };

            if (label.position === "top") {
              labelStyle = {
                ...labelStyle,
                top: moldConfig.centerY - moldConfig.height / 2 - 40,
                left: moldConfig.centerX,
                transform: "translateX(-50%)",
              };
            } else if (label.position === "right") {
              labelStyle = {
                ...labelStyle,
                top: moldConfig.centerY,
                right: 960 - moldConfig.width / 2 - moldConfig.wallThickness - 20,
                transform: "translateY(-50%) translateX(100%)",
              };
            } else if (label.position === "bottom") {
              labelStyle = {
                ...labelStyle,
                bottom: 1080 - moldConfig.centerY - moldConfig.height / 2 - 40,
                left: moldConfig.centerX,
                transform: "translateX(-50%)",
              };
            } else if (label.position === "left") {
              labelStyle = {
                ...labelStyle,
                top: moldConfig.centerY,
                left: moldConfig.centerX - moldConfig.width / 2 - moldConfig.wallThickness - 20,
                transform: "translateY(-50%) translateX(-100%)",
              };
            }

            return (
              <div key={`label-${i}`} style={labelStyle}>
                {label.text}
              </div>
            );
          })}
        </div>
      )}

      {/* Section title */}
      <div
        style={{
          position: "absolute",
          top: 60,
          left: 0,
          right: 0,
          textAlign: "center",
          opacity: moldOpacity,
        }}
      >
        <span
          style={{
            fontSize: 24,
            fontFamily: "sans-serif",
            color: COLORS.WALLS_AMBER,
            fontWeight: "bold",
          }}
        >
          First: tests
        </span>
        <div
          style={{
            fontSize: 16,
            color: COLORS.LABEL_GRAY,
            marginTop: 8,
          }}
        >
          The Constraints
        </div>
      </div>

      {/* Caption */}
      <div
        style={{
          position: "absolute",
          bottom: 60,
          left: 0,
          right: 0,
          textAlign: "center",
          fontSize: 20,
          color: COLORS.LABEL_WHITE,
          fontFamily: "sans-serif",
          opacity: interpolate(frame, [BEATS.HOLD_START, BEATS.HOLD_START + 30], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
        }}
      >
        Tests define the boundaries. Code must fit within them.
      </div>
    </AbsoluteFill>
  );
};
