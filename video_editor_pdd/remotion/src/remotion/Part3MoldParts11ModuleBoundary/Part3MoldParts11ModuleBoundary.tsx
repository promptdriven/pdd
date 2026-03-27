import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";

import { BlueprintGrid } from "./BlueprintGrid";
import { ModuleBox } from "./ModuleBox";
import { ConnectionArrow } from "./ConnectionArrow";
import { BoundaryCircle } from "./BoundaryCircle";
import {
  BG_COLOR,
  GRID_COLOR,
  GRID_OPACITY,
  GRID_SPACING,
  MODULE_FILL,
  CENTER_BORDER_COLOR,
  SURROUNDING_BORDER_COLOR,
  CENTER_LABEL_COLOR,
  SURROUNDING_LABEL_COLOR,
  GLOW_COLOR,
  GLOW_BLUR,
  GLOW_OPACITY,
  ARROW_COLOR,
  ARROW_OPACITY,
  ARROW_WIDTH,
  BOUNDARY_COLOR,
  BOUNDARY_OPACITY,
  BOUNDARY_RADIUS,
  BOUNDARY_LABEL_OPACITY,
  MAIN_LABEL_COLOR,
  SUB_LABEL_COLOR,
  CENTER_X,
  CENTER_Y,
  CENTER_WIDTH,
  CENTER_HEIGHT,
  SURROUND_WIDTH,
  SURROUND_HEIGHT,
  SURROUNDING_MODULES,
} from "./constants";

export const defaultPart3MoldParts11ModuleBoundaryProps = {};

export const Part3MoldParts11ModuleBoundary: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Dimming of surrounding modules (frames 210-240) ───────────
  const surroundDim = interpolate(frame, [210, 240], [1, 0.6], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.sin),
  });

  // ── Main label fade-in (frames 300-320) ───────────────────────
  const mainLabelOpacity = interpolate(frame, [300, 320], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // ── Subtext fade-in (frames 420-440) ──────────────────────────
  const subLabelOpacity = interpolate(frame, [420, 440], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Blueprint grid */}
      <BlueprintGrid
        spacing={GRID_SPACING}
        color={GRID_COLOR}
        opacity={GRID_OPACITY}
      />

      {/* SVG layer for all diagram elements */}
      <AbsoluteFill>
        <svg
          width={1920}
          height={1080}
          viewBox="0 0 1920 1080"
          style={{ position: "absolute", top: 0, left: 0 }}
        >
          {/* ── Connection arrows (appear from frame 90) ─────── */}
          {SURROUNDING_MODULES.map((mod, i) => (
            <ConnectionArrow
              key={`arrow-${mod.name}`}
              fromX={CENTER_X}
              fromY={CENTER_Y}
              toX={mod.x}
              toY={mod.y}
              color={ARROW_COLOR}
              opacity={ARROW_OPACITY}
              strokeWidth={ARROW_WIDTH}
              dashed={mod.async}
              drawStart={90 + i * 5}
              drawDuration={20}
              opacityMultiplier={surroundDim}
            />
          ))}

          {/* ── Boundary circle (appears from frame 150) ─────── */}
          <BoundaryCircle
            cx={CENTER_X}
            cy={CENTER_Y}
            radius={BOUNDARY_RADIUS}
            color={BOUNDARY_COLOR}
            circleOpacity={BOUNDARY_OPACITY}
            strokeWidth={2}
            animStart={150}
            animDuration={30}
            labelText="PDD boundary"
            labelColor={BOUNDARY_COLOR}
            labelOpacity={BOUNDARY_LABEL_OPACITY}
            labelSize={11}
            labelDelay={15}
          />

          {/* ── Central module (visible from frame 0) ────────── */}
          <ModuleBox
            label="user_parser"
            x={CENTER_X}
            y={CENTER_Y}
            width={CENTER_WIDTH}
            height={CENTER_HEIGHT}
            borderColor={CENTER_BORDER_COLOR}
            borderWidth={2}
            borderRadius={12}
            fillColor={MODULE_FILL}
            labelColor={CENTER_LABEL_COLOR}
            labelSize={14}
            labelWeight={700}
            glowColor={GLOW_COLOR}
            glowBlur={GLOW_BLUR}
            glowOpacity={GLOW_OPACITY}
            fadeInStart={0}
          />

          {/* ── Surrounding modules (staggered from frame 30) ── */}
          {SURROUNDING_MODULES.map((mod, i) => (
            <ModuleBox
              key={mod.name}
              label={mod.name}
              x={mod.x}
              y={mod.y}
              width={SURROUND_WIDTH}
              height={SURROUND_HEIGHT}
              borderColor={SURROUNDING_BORDER_COLOR}
              borderWidth={1}
              borderRadius={8}
              fillColor={MODULE_FILL}
              labelColor={SURROUNDING_LABEL_COLOR}
              labelSize={12}
              labelWeight={400}
              fadeInStart={30 + i * 10}
              opacityMultiplier={surroundDim}
            />
          ))}

          {/* ── Main label ───────────────────────────────────── */}
          <text
            x={CENTER_X}
            y={800}
            textAnchor="middle"
            fontFamily="Inter, sans-serif"
            fontSize={22}
            fontWeight={600}
            fill={MAIN_LABEL_COLOR}
            opacity={mainLabelOpacity}
          >
            PDD operates at the module level.
          </text>

          {/* ── Subtext ──────────────────────────────────────── */}
          <text
            x={CENTER_X}
            y={840}
            textAnchor="middle"
            fontFamily="Inter, sans-serif"
            fontSize={14}
            fontWeight={400}
            fill={SUB_LABEL_COLOR}
            opacity={subLabelOpacity}
          >
            The mold makes each part precise. The assembly is still yours.
          </text>
        </svg>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part3MoldParts11ModuleBoundary;
