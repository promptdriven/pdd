import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";

const WIDTH = 1920;
const HEIGHT = 1080;
const FONT_FAMILY = "Inter, sans-serif";

interface GapAnnotationProps {
  x: number;
  y: number;
  fadeInStart: number;
  fadeInEnd: number;
  fadeOutStart: number;
  fadeOutEnd: number;
}

export const GapAnnotation: React.FC<GapAnnotationProps> = ({
  x,
  y,
  fadeInStart,
  fadeInEnd,
  fadeOutStart,
  fadeOutEnd,
}) => {
  const frame = useCurrentFrame();

  const fadeInOpacity = interpolate(
    frame,
    [fadeInStart, fadeInEnd],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    },
  );

  const fadeOutOpacity = interpolate(
    frame,
    [fadeOutStart, fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    },
  );

  const opacity = Math.min(fadeInOpacity, fadeOutOpacity);

  if (frame < fadeInStart) return null;

  const arrowStartY = y + 40;
  const arrowEndY = y + 90;
  const arrowHeadSize = 8;

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Text shadow filter */}
        <defs>
          <filter id="annotationShadow" x="-20%" y="-20%" width="140%" height="140%">
            <feDropShadow dx="0" dy="2" stdDeviation="4" floodColor="rgba(0,0,0,0.6)" />
          </filter>
        </defs>

        {/* Annotation text */}
        <text
          x={x}
          y={y}
          fill="#FFFFFF"
          fontSize={28}
          fontFamily={FONT_FAMILY}
          fontWeight={600}
          textAnchor="middle"
          opacity={opacity}
          filter="url(#annotationShadow)"
        >
          The gap compounds
        </text>

        {/* Downward arrow line */}
        <line
          x1={x}
          y1={arrowStartY}
          x2={x}
          y2={arrowEndY}
          stroke="#FFFFFF"
          strokeWidth={2}
          opacity={opacity * 0.8}
        />

        {/* Arrow head */}
        <polygon
          points={`${x},${arrowEndY + arrowHeadSize} ${x - arrowHeadSize},${arrowEndY} ${x + arrowHeadSize},${arrowEndY}`}
          fill="#FFFFFF"
          opacity={opacity * 0.8}
        />
      </svg>
    </AbsoluteFill>
  );
};

export default GapAnnotation;
