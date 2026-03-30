// NoiseTexture.tsx — subtle paper-grain overlay via SVG feTurbulence
import React from "react";
import { AbsoluteFill } from "remotion";

interface NoiseTextureProps {
  color: string;
  opacity: number;
}

const NoiseTexture: React.FC<NoiseTextureProps> = ({ color, opacity }) => {
  return (
    <AbsoluteFill style={{ opacity, mixBlendMode: "overlay" }}>
      <svg
        width="100%"
        height="100%"
        xmlns="http://www.w3.org/2000/svg"
        style={{ position: "absolute", inset: 0 }}
      >
        <filter id="noiseFilter">
          <feTurbulence
            type="fractalNoise"
            baseFrequency="0.65"
            numOctaves={3}
            stitchTiles="stitch"
          />
          <feColorMatrix
            type="saturate"
            values="0"
          />
        </filter>
        <rect
          width="100%"
          height="100%"
          filter="url(#noiseFilter)"
          fill={color}
        />
      </svg>
    </AbsoluteFill>
  );
};

export default NoiseTexture;
