import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface HandwrittenTextProps {
  text: string;
  fontSize: number;
  color: string;
  centerX: number;
  centerY: number;
  rotation: number;
  strokeWriteStart: number;
  strokeWriteEnd: number;
}

/**
 * Simulates handwritten text appearing via an SVG stroke-dashoffset reveal.
 * We render the text as an SVG <text> element with a stroke, then animate
 * the dashoffset from full-length to 0 to create a "writing" effect.
 *
 * Since we can't get the exact path length of text glyphs at build time,
 * we use a generous dasharray value and also fade in the fill behind it.
 */
export const HandwrittenText: React.FC<HandwrittenTextProps> = ({
  text,
  fontSize,
  color,
  centerX,
  centerY,
  rotation,
  strokeWriteStart,
  strokeWriteEnd,
}) => {
  const frame = useCurrentFrame();

  const writeDuration = strokeWriteEnd - strokeWriteStart;

  // Stroke reveal progress: 0 → 1
  const strokeProgress = interpolate(
    frame,
    [strokeWriteStart, strokeWriteEnd],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.quad),
    }
  );

  // Fill opacity fades in slightly behind the stroke
  const fillOpacity = interpolate(
    frame,
    [strokeWriteStart + writeDuration * 0.3, strokeWriteEnd],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Use a generous total length for dasharray
  const totalLength = 2000;
  const dashOffset = totalLength * (1 - strokeProgress);

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: 1920,
        height: 1080,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        pointerEvents: "none",
      }}
    >
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <g transform={`rotate(${rotation}, ${centerX}, ${centerY})`}>
          {/* Stroke layer — the "writing" animation */}
          <text
            x={centerX}
            y={centerY}
            textAnchor="middle"
            dominantBaseline="central"
            fontFamily="'Caveat', 'Segoe Script', 'Comic Sans MS', cursive"
            fontSize={fontSize}
            fill="none"
            stroke={color}
            strokeWidth={2}
            strokeDasharray={totalLength}
            strokeDashoffset={dashOffset}
          >
            {text}
          </text>

          {/* Fill layer — fades in behind the stroke */}
          <text
            x={centerX}
            y={centerY}
            textAnchor="middle"
            dominantBaseline="central"
            fontFamily="'Caveat', 'Segoe Script', 'Comic Sans MS', cursive"
            fontSize={fontSize}
            fill={color}
            fillOpacity={fillOpacity}
          >
            {text}
          </text>
        </g>
      </svg>
    </div>
  );
};

export default HandwrittenText;
