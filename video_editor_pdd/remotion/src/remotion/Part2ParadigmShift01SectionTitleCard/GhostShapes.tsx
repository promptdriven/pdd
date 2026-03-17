import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MOLD_X,
  MOLD_Y,
  CIRCUIT_X,
  CIRCUIT_Y,
  MOLD_COLOR,
  CIRCUIT_COLOR,
  GHOST_OPACITY,
  GHOST_STROKE_WIDTH,
  GHOST_GLOW_BLUR,
  GHOST_GLOW_OPACITY,
  GHOST_DRAW_START,
  GHOST_DRAW_END,
  PULSE_START,
  PULSE_CYCLE_FRAMES,
  TOTAL_FRAMES,
} from "./constants";

/**
 * Simplified injection mold cavity cross-section:
 * A rectangular cavity shape with a tapered nozzle at top.
 */
const moldPath =
  "M -40 -50 L -40 50 L 40 50 L 40 -50 L 15 -50 L 8 -70 L -8 -70 L -15 -50 Z";

/**
 * Simplified circuit schematic fragment:
 * AND/OR gate shapes with connecting wires.
 */
const circuitPath =
  "M -60 -20 L -30 -20 M -60 20 L -30 20 " + // input wires
  "M -30 -30 L -30 30 Q 10 30 10 0 Q 10 -30 -30 -30 " + // AND gate body
  "M 10 0 L 40 0 " + // output wire
  "M 40 -15 L 40 15 L 60 0 Z " + // triangle (OR-ish)
  "M 60 0 L 80 0"; // final output

const MOLD_PATH_LENGTH = 340;
const CIRCUIT_PATH_LENGTH = 380;

export const GhostShapes: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [GHOST_DRAW_START, GHOST_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const moldDashOffset = MOLD_PATH_LENGTH * (1 - drawProgress);
  const circuitDashOffset = CIRCUIT_PATH_LENGTH * (1 - drawProgress);

  // Gentle amber pulse on mold after frame 90
  const pulseProgress =
    frame >= PULSE_START
      ? ((frame - PULSE_START) % PULSE_CYCLE_FRAMES) / PULSE_CYCLE_FRAMES
      : 0;
  const pulseGlow = interpolate(
    Math.sin(pulseProgress * Math.PI * 2),
    [-1, 1],
    [GHOST_GLOW_OPACITY, GHOST_GLOW_OPACITY * 3],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <filter id="moldGlow">
            <feGaussianBlur stdDeviation={GHOST_GLOW_BLUR} result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
          <filter id="circuitGlow">
            <feGaussianBlur stdDeviation={GHOST_GLOW_BLUR} result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Mold cavity outline */}
        <g transform={`translate(${MOLD_X}, ${MOLD_Y})`}>
          {/* Glow layer */}
          <path
            d={moldPath}
            fill="none"
            stroke={MOLD_COLOR}
            strokeWidth={GHOST_STROKE_WIDTH + 4}
            opacity={frame >= PULSE_START ? pulseGlow : GHOST_GLOW_OPACITY}
            filter="url(#moldGlow)"
            strokeDasharray={MOLD_PATH_LENGTH}
            strokeDashoffset={moldDashOffset}
          />
          {/* Main stroke */}
          <path
            d={moldPath}
            fill="none"
            stroke={MOLD_COLOR}
            strokeWidth={GHOST_STROKE_WIDTH}
            opacity={GHOST_OPACITY}
            strokeDasharray={MOLD_PATH_LENGTH}
            strokeDashoffset={moldDashOffset}
          />
        </g>

        {/* Circuit schematic fragment */}
        <g transform={`translate(${CIRCUIT_X}, ${CIRCUIT_Y})`}>
          {/* Glow layer */}
          <path
            d={circuitPath}
            fill="none"
            stroke={CIRCUIT_COLOR}
            strokeWidth={GHOST_STROKE_WIDTH + 4}
            opacity={GHOST_GLOW_OPACITY}
            filter="url(#circuitGlow)"
            strokeDasharray={CIRCUIT_PATH_LENGTH}
            strokeDashoffset={circuitDashOffset}
          />
          {/* Main stroke */}
          <path
            d={circuitPath}
            fill="none"
            stroke={CIRCUIT_COLOR}
            strokeWidth={GHOST_STROKE_WIDTH}
            opacity={GHOST_OPACITY}
            strokeDasharray={CIRCUIT_PATH_LENGTH}
            strokeDashoffset={circuitDashOffset}
          />
        </g>
      </svg>
    </AbsoluteFill>
  );
};

export default GhostShapes;
