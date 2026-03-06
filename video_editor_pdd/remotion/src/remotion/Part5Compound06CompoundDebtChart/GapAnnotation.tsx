import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";

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
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Annotation text with shadow */}
        <text
          x={x}
          y={y}
          fill="#FFFFFF"
          fontSize={28}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
          textAnchor="middle"
          opacity={opacity}
          style={{
            textShadow: "0 2px 8px rgba(0, 0, 0, 0.6)",
          }}
        >
          {text}
        </text>

        {/* Drop shadow filter for SVG text */}
        <defs>
          <filter id="textShadow" x="-20%" y="-20%" width="140%" height="140%">
            <feDropShadow
              dx={0}
              dy={2}
              stdDeviation={4}
              floodColor="rgba(0,0,0,0.6)"
            />
          </filter>
        </defs>

        {/* Shadow text underneath */}
        <text
          x={x}
          y={y}
          fill="#FFFFFF"
          fontSize={28}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
          textAnchor="middle"
          opacity={opacity}
          filter="url(#textShadow)"
        >
          {text}
        </text>

        {/* Downward arrow */}
        <g opacity={opacity}>
          {/* Arrow shaft */}
          <line
            x1={x}
            y1={y + 12}
            x2={x}
            y2={y + 55}
            stroke="#FFFFFF"
            strokeWidth={2}
            opacity={0.8}
          />
          {/* Arrowhead */}
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
