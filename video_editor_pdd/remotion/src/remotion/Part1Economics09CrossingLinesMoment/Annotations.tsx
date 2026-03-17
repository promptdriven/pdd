import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  FONT_FAMILY,
  AXIS_LABEL_COLOR,
  RED_FORK_COLOR,
  ANNOTATION_SAME_TOOLS_START,
  ANNOTATION_SAME_TOOLS_FADE,
  METR_ANNOTATION_START,
  METR_FADE_DURATION,
  dataToPixelX,
  dataToPixelY,
} from "./constants";

/**
 * Annotations: Renders the "Same tools. Different codebase sizes." text,
 * METR annotation, and connecting lines between the two forks.
 */
export const Annotations: React.FC = () => {
  const frame = useCurrentFrame();

  // "Same tools" annotation fades in
  const sameToolsOpacity = interpolate(
    frame,
    [ANNOTATION_SAME_TOOLS_START, ANNOTATION_SAME_TOOLS_START + ANNOTATION_SAME_TOOLS_FADE],
    [0, 0.5],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // METR annotations fade in
  const metrOpacity = interpolate(
    frame,
    [METR_ANNOTATION_START, METR_ANNOTATION_START + METR_FADE_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Positions for annotations (between the two forks around 2023)
  const annotX = dataToPixelX(2022.5);
  // Midpoint between upper fork (~10h at 2022) and lower fork (~4h at 2022)
  const annotY = dataToPixelY(7);

  // Upper fork endpoint for METR annotation
  const metrX = dataToPixelX(2024.5);
  const metrY = dataToPixelY(11.5);

  // Connecting lines from annotation to each fork
  const lowerY = dataToPixelY(4); // small codebase at 2022
  const upperY = dataToPixelY(10); // large codebase at 2022

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* "Same tools" annotation */}
        {frame >= ANNOTATION_SAME_TOOLS_START && (
          <g opacity={sameToolsOpacity}>
            {/* Connecting dashed lines to both forks */}
            <line
              x1={annotX}
              y1={annotY - 8}
              x2={annotX}
              y2={upperY + 4}
              stroke={AXIS_LABEL_COLOR}
              strokeWidth={1}
              strokeDasharray="3 3"
              opacity={0.15}
            />
            <line
              x1={annotX}
              y1={annotY + 8}
              x2={annotX}
              y2={lowerY - 4}
              stroke={AXIS_LABEL_COLOR}
              strokeWidth={1}
              strokeDasharray="3 3"
              opacity={0.15}
            />

            {/* Text */}
            <text
              x={annotX}
              y={annotY}
              fill={AXIS_LABEL_COLOR}
              fontSize={12}
              fontFamily={FONT_FAMILY}
              fontWeight={400}
              textAnchor="middle"
            >
              Same tools. Different codebase sizes.
            </text>
          </g>
        )}

        {/* METR annotations near upper fork endpoint */}
        {frame >= METR_ANNOTATION_START && (
          <g>
            <text
              x={metrX}
              y={metrY - 28}
              fill={RED_FORK_COLOR}
              fontSize={9}
              fontFamily={FONT_FAMILY}
              fontWeight={400}
              textAnchor="middle"
              opacity={metrOpacity * 0.45}
            >
              METR, 2025: experienced devs 19% slower
            </text>
            <text
              x={metrX}
              y={metrY - 14}
              fill={RED_FORK_COLOR}
              fontSize={9}
              fontFamily={FONT_FAMILY}
              fontWeight={400}
              textAnchor="middle"
              opacity={metrOpacity * 0.35}
            >
              {"Developers believed +20%. Reality: \u221219%."}
            </text>
          </g>
        )}
      </svg>
    </AbsoluteFill>
  );
};

export default Annotations;
