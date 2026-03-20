import React, { useMemo } from "react";
import { useCurrentFrame } from "remotion";

interface FilmGrainProps {
  opacity: number;
  grainFps: number;
  width: number;
  height: number;
}

/**
 * Animated monochrome film grain overlay rendered via a canvas-based
 * SVG noise pattern. Updates at a reduced frame-rate (e.g. 12 fps)
 * to mimic real film grain cadence.
 */
const FilmGrain: React.FC<FilmGrainProps> = ({
  opacity,
  grainFps,
  width,
  height,
}) => {
  const frame = useCurrentFrame();

  // Quantise the frame to the grain cadence so the pattern only
  // changes at `grainFps` updates per second.
  const grainFrame = Math.floor(frame / (30 / grainFps));

  // Deterministic pseudo-random noise based on the grain frame.
  const grainSvg = useMemo(() => {
    const seed = grainFrame * 17 + 31;
    const rects: string[] = [];
    const step = 4; // pixel granularity
    for (let y = 0; y < height; y += step) {
      for (let x = 0; x < width; x += step) {
        // Simple LCG hash
        const hash =
          ((x * 374761 + y * 668265 + seed * 982451) % 2147483647) /
          2147483647;
        const brightness = Math.floor(hash * 255);
        rects.push(
          `<rect x="${x}" y="${y}" width="${step}" height="${step}" fill="rgb(${brightness},${brightness},${brightness})" />`
        );
      }
    }
    return `<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}">${rects.join("")}</svg>`;
  }, [grainFrame, width, height]);

  const dataUri = useMemo(
    () =>
      `data:image/svg+xml;base64,${typeof btoa !== "undefined" ? btoa(grainSvg) : Buffer.from(grainSvg).toString("base64")}`,
    [grainSvg]
  );

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width,
        height,
        opacity,
        mixBlendMode: "overlay",
        backgroundImage: `url("${dataUri}")`,
        backgroundSize: `${width}px ${height}px`,
        pointerEvents: "none",
      }}
    />
  );
};

export default FilmGrain;
