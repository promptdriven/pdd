import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

interface CodeBlockProps {
  x: number;
  y: number;
  width: number;
  height: number;
  lines: string[];
  /** Frame at which code generation begins */
  genStart: number;
  /** Frames per line reveal */
  lineRate: number;
  glowColor: string;
  bgColor: string;
  textColor: string;
  textOpacity: number;
}

const CodeBlock: React.FC<CodeBlockProps> = ({
  x,
  y,
  width,
  height,
  lines,
  genStart,
  lineRate,
  glowColor,
  bgColor,
  textColor,
  textOpacity,
}) => {
  const frame = useCurrentFrame();

  const elapsed = Math.max(0, frame - genStart);
  const visibleCount = Math.min(lines.length, Math.floor(elapsed / lineRate));
  const allRevealed = visibleCount >= lines.length;

  // Total frames to reveal all lines
  const totalRevealFrames = lines.length * lineRate;
  const glowStartFrame = genStart + totalRevealFrames;

  // Glow effect once all lines revealed
  const glowOpacity = allRevealed
    ? interpolate(frame, [glowStartFrame, glowStartFrame + 15], [0, 0.7], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.cubic),
      })
    : 0;

  // Block fade-in
  const blockOpacity = interpolate(frame, [genStart, genStart + 10], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        width,
        height,
        opacity: blockOpacity,
      }}
    >
      {/* Glow border */}
      <div
        style={{
          position: "absolute",
          inset: -3,
          borderRadius: 8,
          border: `2px solid ${glowColor}`,
          opacity: glowOpacity,
          boxShadow: `0 0 12px ${glowColor}, 0 0 24px ${glowColor}`,
          pointerEvents: "none",
        }}
      />

      {/* Code container */}
      <div
        style={{
          width: "100%",
          height: "100%",
          backgroundColor: bgColor,
          borderRadius: 6,
          padding: 12,
          overflow: "hidden",
          boxSizing: "border-box",
        }}
      >
        {lines.slice(0, visibleCount).map((line, i) => (
          <div
            key={i}
            style={{
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 11,
              fontWeight: 400,
              color: textColor,
              opacity: textOpacity,
              lineHeight: "16px",
              whiteSpace: "pre",
              height: 16,
            }}
          >
            {line}
          </div>
        ))}
      </div>
    </div>
  );
};

export default CodeBlock;
