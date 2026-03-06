import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import { WIDTH, HEIGHT } from "./constants";

interface GapAnnotationProps {
  text: string;
  x: number;
  y: number;
  fadeInStart: number;
  fadeInEnd: number;
  fadeOutStart: number;
  fadeOutEnd: number;
}

export const GapAnnotation: React.FC<GapAnnotationProps> = ({
  text,
  x,
  y,
  fadeInStart,
  fadeInEnd,
  fadeOutStart,
  fadeOutEnd,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [fadeInStart, fadeInEnd, fadeOutStart, fadeOutEnd],
    [0, 1, 1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  if (frame < fadeInStart) return null;

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <filter id="annotationShadow" x="-20%" y="-20%" width="140%" height="140%">
            <feDropShadow
              dx={0}
              dy={2}
              stdDeviation={4}
              floodColor="rgba(0,0,0,0.6)"
            />
          </filter>
        </defs>

        {/* Annotation text with drop shadow */}
        <text
          x={x}
          y={y}
          fill="#FFFFFF"
          fontSize={28}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
          textAnchor="middle"
          opacity={opacity}
          filter="url(#annotationShadow)"
        >
          {text}
        </text>

        {/* Downward arrow */}
        <g opacity={opacity}>
          <line
            x1={x}
            y1={y + 12}
            x2={x}
            y2={y + 55}
            stroke="#FFFFFF"
            strokeWidth={2}
            opacity={0.8}
          />
          <polygon
            points={`${x - 6},${y + 48} ${x + 6},${y + 48} ${x},${y + 60}`}
            fill="#FFFFFF"
            opacity={0.8}
          />
        </g>
      </svg>
    </AbsoluteFill>
  );
};

export default GapAnnotation;
