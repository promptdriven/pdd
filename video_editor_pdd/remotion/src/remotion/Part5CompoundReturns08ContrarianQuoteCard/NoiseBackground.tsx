import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, Easing, interpolate } from "remotion";
import { COLORS, FRAMES } from "./constants";

/**
 * Deep navy background with a subtle noise grain texture.
 * The noise is created via an SVG feTurbulence filter so it
 * requires no external assets.
 */
export const NoiseBackground: React.FC = () => {
  const frame = useCurrentFrame();

  const bgOpacity = interpolate(frame, [0, FRAMES.bgFadeEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Stable seed so the noise doesn't flicker between frames
  const filterId = useMemo(() => "noise-bg-filter", []);

  return (
    <AbsoluteFill style={{ opacity: bgOpacity }}>
      {/* Solid background */}
      <AbsoluteFill style={{ backgroundColor: COLORS.background }} />

      {/* Noise overlay via SVG filter */}
      <AbsoluteFill>
        <svg width="100%" height="100%" style={{ position: "absolute", top: 0, left: 0 }}>
          <defs>
            <filter id={filterId}>
              <feTurbulence
                type="fractalNoise"
                baseFrequency="0.65"
                numOctaves={3}
                seed={42}
                stitchTiles="stitch"
              />
              <feColorMatrix
                type="matrix"
                values={`0 0 0 0 ${parseInt(COLORS.noiseTexture.slice(1, 3), 16) / 255}
                         0 0 0 0 ${parseInt(COLORS.noiseTexture.slice(3, 5), 16) / 255}
                         0 0 0 0 ${parseInt(COLORS.noiseTexture.slice(5, 7), 16) / 255}
                         0 0 0 0.02 0`}
              />
            </filter>
          </defs>
          <rect width="100%" height="100%" filter={`url(#${filterId})`} />
        </svg>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};
