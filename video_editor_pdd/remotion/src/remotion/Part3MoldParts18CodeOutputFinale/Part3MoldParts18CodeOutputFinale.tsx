import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import MoldCrossSection from "./MoldCrossSection";
import CodeBlock from "./CodeBlock";
import {
  BACKGROUND_COLOR,
  CANVAS_WIDTH,
  CODE_GLOW_COLOR,
  CODE_BORDER_COLOR,
  CODE_BORDER_DIMMED,
  ARROW_COLOR,
  ARROW_OPACITY,
  CODE_FADE_IN_END,
  CODE_GLOW_FADE_START,
  CODE_GLOW_FADE_END,
  MOLD_GLOW_START,
  MOLD_GLOW_END,
  CODE_GLOW_FROM,
  CODE_GLOW_TO,
  CODE_TEXT_FROM,
  CODE_TEXT_TO,
  MOLD_GLOW_FROM,
  MOLD_GLOW_TO,
} from "./constants";

export const defaultPart3MoldParts18CodeOutputFinaleProps = {};

export const Part3MoldParts18CodeOutputFinale: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Code block fade in (frames 0-20) ──
  const codeOverallOpacity = interpolate(frame, [0, CODE_FADE_IN_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // ── Code glow fade (frames 20-40): 0.2 → 0.0 ──
  const codeGlowOpacity = interpolate(
    frame,
    [CODE_GLOW_FADE_START, CODE_GLOW_FADE_END],
    [CODE_GLOW_FROM, CODE_GLOW_TO],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  // ── Code text dim (frames 20-40): 1.0 → 0.4 ──
  const codeTextOpacity = interpolate(
    frame,
    [CODE_GLOW_FADE_START, CODE_GLOW_FADE_END],
    [CODE_TEXT_FROM, CODE_TEXT_TO],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  // ── Code border transition ──
  const borderBlend = interpolate(
    frame,
    [CODE_GLOW_FADE_START, CODE_GLOW_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );
  const codeBorderColor =
    borderBlend < 0.5 ? CODE_BORDER_COLOR : CODE_BORDER_DIMMED;

  // ── Mold glow intensify (frames 40-60): 0.4 → 0.6 ──
  const moldWallsGlow = interpolate(
    frame,
    [MOLD_GLOW_START, MOLD_GLOW_END],
    [MOLD_GLOW_FROM, MOLD_GLOW_TO],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const moldNozzleGlow = interpolate(
    frame,
    [MOLD_GLOW_START, MOLD_GLOW_END],
    [0.3, 0.5],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const moldCavityGlow = interpolate(
    frame,
    [MOLD_GLOW_START, MOLD_GLOW_END],
    [0.1, 0.2],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Arrow opacity (visible from frame 0, subtle) ──
  const arrowOpacity = interpolate(frame, [0, CODE_FADE_IN_END], [0, ARROW_OPACITY], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const arrowX = CANVAS_WIDTH / 2;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Mold cross-section (persistent, glow intensifies) */}
      <MoldCrossSection
        wallsGlow={moldWallsGlow}
        nozzleGlow={moldNozzleGlow}
        cavityGlow={moldCavityGlow}
      />

      {/* Hierarchy arrow: mold → code */}
      <svg
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: CANVAS_WIDTH,
          height: 1080,
          pointerEvents: "none",
        }}
      >
        <defs>
          <marker
            id="arrowhead"
            markerWidth="8"
            markerHeight="6"
            refX="8"
            refY="3"
            orient="auto"
          >
            <polygon
              points="0 0, 8 3, 0 6"
              fill={ARROW_COLOR}
              opacity={arrowOpacity / ARROW_OPACITY}
            />
          </marker>
        </defs>
        <line
          x1={arrowX}
          y1={530}
          x2={arrowX}
          y2={640}
          stroke={ARROW_COLOR}
          strokeWidth={1.5}
          opacity={arrowOpacity}
          markerEnd="url(#arrowhead)"
        />
      </svg>

      {/* Code output block */}
      <CodeBlock
        glowOpacity={codeGlowOpacity}
        glowColor={CODE_GLOW_COLOR}
        textOpacity={codeTextOpacity}
        borderColor={codeBorderColor}
        overallOpacity={codeOverallOpacity}
      />
    </AbsoluteFill>
  );
};

export default Part3MoldParts18CodeOutputFinale;
