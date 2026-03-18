import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { TEXT_PRIMARY, AMBER, TIMING, CODE_SNIPPET } from "./constants";

/**
 * Code snippet that appears below the mold diagram.
 * Glows briefly then fades — "The code is output. The mold is what matters."
 */
export const CodeOutput: React.FC = () => {
  const frame = useCurrentFrame();

  // Code fade in (frame 370-390)
  const codeOpacity = interpolate(
    frame,
    [TIMING.codeStart, TIMING.codeStart + 20],
    [0, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Glow effect (frames 370-420, then fades)
  const glowOpacity = interpolate(
    frame,
    [TIMING.codeStart, TIMING.codeStart + 10, TIMING.codeGlowEnd - 10, TIMING.codeGlowEnd],
    [0, 0.15, 0.15, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
  );

  // Code dims after glow (frames 420-440)
  const dimFactor = interpolate(
    frame,
    [TIMING.codeDimStart, TIMING.codeDimStart + 20],
    [1, 0.33], // 0.6 * 0.33 ≈ 0.2
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const finalOpacity = codeOpacity * dimFactor;

  // Caption fade (frame 450-465)
  const captionOpacity = interpolate(
    frame,
    [TIMING.captionStart, TIMING.captionStart + 15],
    [0, 0.7],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  if (frame < TIMING.codeStart) return null;

  return (
    <>
      {/* Code block positioned below the mold diagram */}
      <div
        style={{
          position: "absolute",
          left: 150,
          top: 830,
          width: 400,
          padding: "12px 16px",
          borderRadius: 8,
          backgroundColor: `rgba(30, 41, 59, ${finalOpacity * 0.5})`,
        }}
      >
        {/* Glow effect */}
        {glowOpacity > 0 && (
          <div
            style={{
              position: "absolute",
              inset: -8,
              borderRadius: 16,
              backgroundColor: TEXT_PRIMARY,
              opacity: glowOpacity,
              filter: "blur(16px)",
              pointerEvents: "none",
            }}
          />
        )}

        <pre
          style={{
            margin: 0,
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: 10,
            lineHeight: 1.5,
            color: TEXT_PRIMARY,
            opacity: finalOpacity,
            whiteSpace: "pre-wrap",
          }}
        >
          {CODE_SNIPPET}
        </pre>
      </div>

      {/* Final caption */}
      {frame >= TIMING.captionStart && (
        <div
          style={{
            position: "absolute",
            left: 0,
            right: 0,
            top: 990,
            textAlign: "center",
            opacity: captionOpacity,
          }}
        >
          <span
            style={{
              fontFamily: "Inter, sans-serif",
              fontSize: 14,
              color: AMBER,
            }}
          >
            The code is output. The mold is what matters.
          </span>
        </div>
      )}
    </>
  );
};
