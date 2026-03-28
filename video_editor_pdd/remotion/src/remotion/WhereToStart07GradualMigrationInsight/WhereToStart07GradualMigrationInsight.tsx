import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import { BlueprintGrid } from "./BlueprintGrid";
import { FillContainer } from "./FillContainer";
import { ParticleArc } from "./ParticleArc";
import {
  BG_COLOR,
  CODE_CONTAINER_X,
  CODE_CONTAINER_Y,
  CODE_BORDER_COLOR,
  CODE_FILL_COLOR,
  CODE_FILL_OPACITY,
  CODE_START_LEVEL,
  CODE_END_LEVEL,
  CODE_LABEL_COLOR,
  SPEC_CONTAINER_X,
  SPEC_CONTAINER_Y,
  SPEC_BORDER_COLOR,
  SPEC_FILL_COLOR,
  SPEC_FILL_OPACITY,
  SPEC_START_LEVEL,
  SPEC_END_LEVEL,
  SPEC_LABEL_COLOR,
  LABEL_Y,
  LABEL_FONT_SIZE,
  LABEL_FONT_WEIGHT,
  THESIS_Y,
  THESIS_FONT_SIZE,
  THESIS_FONT_WEIGHT,
  THESIS_TEXT_COLOR,
  THESIS_ACCENT_COLOR,
  THESIS_START_FRAME,
  FADE_IN_DURATION,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
} from "./constants";

export const defaultWhereToStart07GradualMigrationInsightProps = {};

export const WhereToStart07GradualMigrationInsight: React.FC = () => {
  const frame = useCurrentFrame();

  // Thesis text fade-in: starts at THESIS_START_FRAME, takes FADE_IN_DURATION frames
  const thesisOpacity = interpolate(
    frame,
    [THESIS_START_FRAME, THESIS_START_FRAME + FADE_IN_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        overflow: "hidden",
      }}
    >
      {/* Blueprint grid background */}
      <BlueprintGrid />

      {/* Code container (left, draining) */}
      <FillContainer
        x={CODE_CONTAINER_X}
        y={CODE_CONTAINER_Y}
        borderColor={CODE_BORDER_COLOR}
        fillColor={CODE_FILL_COLOR}
        fillOpacity={CODE_FILL_OPACITY}
        startLevel={CODE_START_LEVEL}
        endLevel={CODE_END_LEVEL}
        label="CODE"
        labelColor={CODE_LABEL_COLOR}
        labelY={LABEL_Y}
        labelFontSize={LABEL_FONT_SIZE}
        labelFontWeight={LABEL_FONT_WEIGHT}
      />

      {/* Specification container (right, filling) */}
      <FillContainer
        x={SPEC_CONTAINER_X}
        y={SPEC_CONTAINER_Y}
        borderColor={SPEC_BORDER_COLOR}
        fillColor={SPEC_FILL_COLOR}
        fillOpacity={SPEC_FILL_OPACITY}
        startLevel={SPEC_START_LEVEL}
        endLevel={SPEC_END_LEVEL}
        label="SPECIFICATION"
        labelColor={SPEC_LABEL_COLOR}
        labelY={LABEL_Y}
        labelFontSize={LABEL_FONT_SIZE}
        labelFontWeight={LABEL_FONT_WEIGHT}
      />

      {/* Flow arc particles connecting the two containers */}
      <ParticleArc />

      {/* Thesis text: "from code to specification" */}
      <div
        style={{
          position: "absolute",
          left: CANVAS_WIDTH / 2,
          top: THESIS_Y,
          transform: "translateX(-50%)",
          opacity: thesisOpacity,
          fontFamily: "Inter, sans-serif",
          fontSize: THESIS_FONT_SIZE,
          fontWeight: THESIS_FONT_WEIGHT,
          whiteSpace: "nowrap",
          display: "flex",
          alignItems: "center",
        }}
      >
        <span style={{ color: THESIS_TEXT_COLOR }}>from code to </span>
        <span style={{ color: THESIS_ACCENT_COLOR }}>specification</span>
      </div>
    </AbsoluteFill>
  );
};

export default WhereToStart07GradualMigrationInsight;
