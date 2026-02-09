import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, MOLD, CrossSectionIntroPropsType } from "./constants";

export const CrossSectionIntro: React.FC<CrossSectionIntroPropsType> = ({
  showLabels = true,
}) => {
  const frame = useCurrentFrame();

  // Animation progress values
  const outlineOpacity = interpolate(
    frame,
    [BEATS.OUTLINE_START, BEATS.OUTLINE_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Walls: fade in with pulse (90-150)
  const wallsGlow = interpolate(
    frame,
    [BEATS.WALLS_START, BEATS.WALLS_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Pulse effect for walls (subtle oscillation using easeInOutSine)
  const wallsPulse = frame >= BEATS.WALLS_START && frame < BEATS.WALLS_START + 40
    ? interpolate(
        frame,
        [BEATS.WALLS_START, BEATS.WALLS_START + 20, BEATS.WALLS_START + 40],
        [0, 0.3, 0],
        { easing: Easing.inOut(Easing.sin) }
      )
    : 0;

  const wallsLabelOpacity = showLabels
    ? interpolate(
        frame,
        [BEATS.WALLS_START, BEATS.WALLS_START + 30],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
      )
    : 0;

  // Nozzle: fade in with pulse (150-210)
  const nozzleGlow = interpolate(
    frame,
    [BEATS.NOZZLE_START, BEATS.NOZZLE_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Pulse effect for nozzle
  const nozzlePulse = frame >= BEATS.NOZZLE_START && frame < BEATS.NOZZLE_START + 40
    ? interpolate(
        frame,
        [BEATS.NOZZLE_START, BEATS.NOZZLE_START + 20, BEATS.NOZZLE_START + 40],
        [0, 0.3, 0],
        { easing: Easing.inOut(Easing.sin) }
      )
    : 0;

  const nozzleLabelOpacity = showLabels
    ? interpolate(
        frame,
        [BEATS.NOZZLE_START, BEATS.NOZZLE_START + 30],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
      )
    : 0;

  // Material: fade in with pulse (210-270)
  const materialGlow = interpolate(
    frame,
    [BEATS.MATERIAL_START, BEATS.MATERIAL_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Pulse effect for material
  const materialPulse = frame >= BEATS.MATERIAL_START && frame < BEATS.MATERIAL_START + 40
    ? interpolate(
        frame,
        [BEATS.MATERIAL_START, BEATS.MATERIAL_START + 20, BEATS.MATERIAL_START + 40],
        [0, 0.3, 0],
        { easing: Easing.inOut(Easing.sin) }
      )
    : 0;

  const materialLabelOpacity = showLabels
    ? interpolate(
        frame,
        [BEATS.MATERIAL_START, BEATS.MATERIAL_START + 30],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
      )
    : 0;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      <svg width="100%" height="100%" viewBox="0 0 1920 1080">
        {/* Outer mold outline */}
        <g opacity={outlineOpacity}>
          <rect
            x={MOLD.centerX - MOLD.outerWidth / 2}
            y={MOLD.centerY - MOLD.outerHeight / 2}
            width={MOLD.outerWidth}
            height={MOLD.outerHeight}
            fill="none"
            stroke={COLORS.OUTLINE_GRAY}
            strokeWidth={3}
            rx={12}
          />
        </g>

        {/* Walls (amber) */}
        <g opacity={outlineOpacity}>
          {/* Left wall */}
          <rect
            x={MOLD.centerX - MOLD.outerWidth / 2}
            y={MOLD.centerY - MOLD.outerHeight / 2}
            width={MOLD.wallThickness}
            height={MOLD.outerHeight}
            fill={`rgba(217, 148, 74, ${0.3 + 0.4 * wallsGlow + wallsPulse})`}
            stroke={COLORS.WALLS_AMBER}
            strokeWidth={2}
            style={{
              filter: wallsGlow > 0 ? `drop-shadow(0 0 ${20 * wallsGlow + 15 * wallsPulse}px ${COLORS.WALLS_AMBER})` : "none",
            }}
          />
          {/* Right wall */}
          <rect
            x={MOLD.centerX + MOLD.outerWidth / 2 - MOLD.wallThickness}
            y={MOLD.centerY - MOLD.outerHeight / 2}
            width={MOLD.wallThickness}
            height={MOLD.outerHeight}
            fill={`rgba(217, 148, 74, ${0.3 + 0.4 * wallsGlow + wallsPulse})`}
            stroke={COLORS.WALLS_AMBER}
            strokeWidth={2}
            style={{
              filter: wallsGlow > 0 ? `drop-shadow(0 0 ${20 * wallsGlow + 15 * wallsPulse}px ${COLORS.WALLS_AMBER})` : "none",
            }}
          />
          {/* Bottom wall */}
          <rect
            x={MOLD.centerX - MOLD.outerWidth / 2 + MOLD.wallThickness}
            y={MOLD.centerY + MOLD.outerHeight / 2 - MOLD.wallThickness}
            width={MOLD.outerWidth - 2 * MOLD.wallThickness}
            height={MOLD.wallThickness}
            fill={`rgba(217, 148, 74, ${0.3 + 0.4 * wallsGlow + wallsPulse})`}
            stroke={COLORS.WALLS_AMBER}
            strokeWidth={2}
            style={{
              filter: wallsGlow > 0 ? `drop-shadow(0 0 ${20 * wallsGlow + 15 * wallsPulse}px ${COLORS.WALLS_AMBER})` : "none",
            }}
          />
        </g>

        {/* Nozzle (blue) */}
        <g opacity={outlineOpacity}>
          <rect
            x={MOLD.centerX - MOLD.nozzleWidth / 2}
            y={MOLD.centerY - MOLD.outerHeight / 2 - MOLD.nozzleHeight}
            width={MOLD.nozzleWidth}
            height={MOLD.nozzleHeight + 10}
            fill={`rgba(74, 144, 217, ${0.3 + 0.4 * nozzleGlow + nozzlePulse})`}
            stroke={COLORS.NOZZLE_BLUE}
            strokeWidth={2}
            rx={8}
            style={{
              filter: nozzleGlow > 0 ? `drop-shadow(0 0 ${20 * nozzleGlow + 15 * nozzlePulse}px ${COLORS.NOZZLE_BLUE})` : "none",
            }}
          />
        </g>

        {/* Interior/Material space (green) */}
        <g opacity={outlineOpacity}>
          <rect
            x={MOLD.centerX - MOLD.outerWidth / 2 + MOLD.wallThickness + 10}
            y={MOLD.centerY - MOLD.outerHeight / 2 + 10}
            width={MOLD.outerWidth - 2 * MOLD.wallThickness - 20}
            height={MOLD.outerHeight - MOLD.wallThickness - 20}
            fill={`rgba(90, 170, 110, ${0.1 + 0.2 * materialGlow + materialPulse * 0.3})`}
            stroke={COLORS.MATERIAL_GREEN}
            strokeWidth={1}
            strokeDasharray="8 4"
            rx={4}
            style={{
              filter: materialGlow > 0 ? `drop-shadow(0 0 ${15 * materialGlow + 15 * materialPulse}px ${COLORS.MATERIAL_GREEN})` : "none",
            }}
          />
        </g>
      </svg>

      {/* Labels */}
      {showLabels && (
        <>
          {/* Walls label */}
          {wallsLabelOpacity > 0 && (
            <div
              style={{
                position: "absolute",
                left: MOLD.centerX - MOLD.outerWidth / 2 - 150,
                top: MOLD.centerY - 10,
                fontSize: 24,
                fontWeight: "bold",
                color: COLORS.WALLS_AMBER,
                fontFamily: "sans-serif",
                opacity: wallsLabelOpacity,
              }}
            >
              Walls
            </div>
          )}

          {/* Nozzle label */}
          {nozzleLabelOpacity > 0 && (
            <div
              style={{
                position: "absolute",
                left: MOLD.centerX + MOLD.nozzleWidth / 2 + 20,
                top: MOLD.centerY - MOLD.outerHeight / 2 - MOLD.nozzleHeight / 2 - 10,
                fontSize: 24,
                fontWeight: "bold",
                color: COLORS.NOZZLE_BLUE,
                fontFamily: "sans-serif",
                opacity: nozzleLabelOpacity,
              }}
            >
              Nozzle
            </div>
          )}

          {/* Material label */}
          {materialLabelOpacity > 0 && (
            <div
              style={{
                position: "absolute",
                left: MOLD.centerX + MOLD.outerWidth / 2 + 20,
                top: MOLD.centerY - 10,
                fontSize: 24,
                fontWeight: "bold",
                color: COLORS.MATERIAL_GREEN,
                fontFamily: "sans-serif",
                opacity: materialLabelOpacity,
              }}
            >
              Material
            </div>
          )}
        </>
      )}

      {/* Title */}
      <div
        style={{
          position: "absolute",
          bottom: 60,
          left: 0,
          right: 0,
          textAlign: "center",
          fontSize: 28,
          color: COLORS.LABEL_WHITE,
          fontFamily: "sans-serif",
          opacity: outlineOpacity,
        }}
      >
        The Mold Has Three Parts
      </div>
    </AbsoluteFill>
  );
};
