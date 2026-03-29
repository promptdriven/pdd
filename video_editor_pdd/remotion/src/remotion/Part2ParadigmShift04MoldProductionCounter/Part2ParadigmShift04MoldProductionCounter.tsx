import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  staticFile,
  OffthreadVideo,
} from "remotion";
import { BG_COLOR, TOTAL_FRAMES } from "./constants";
import { MoldCycleAnimation } from "./MoldCycleAnimation";
import { ExponentialCounter } from "./ExponentialCounter";
import { ProgressBar } from "./ProgressBar";

export const defaultPart2ParadigmShift04MoldProductionCounterProps = {};

/**
 * Section 2.4 — Mold Production Counter
 *
 * An animated counter overlay on a cinematic background showing injection molded
 * parts ejecting in rapid succession. A 2D mold animation cycles faster and faster
 * while an exponential counter climbs from 1 to 10,000.
 *
 * Duration: ~10s (300 frames @ 30fps)
 */
export const Part2ParadigmShift04MoldProductionCounter: React.FC = () => {
  const frame = useCurrentFrame();

  // Background video opacity — fade in quickly, stay visible
  const videoOpacity = interpolate(frame, [0, 15], [0.3, 0.45], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Subtle vignette effect that intensifies over time
  const vignetteIntensity = interpolate(frame, [0, TOTAL_FRAMES], [0.5, 0.75], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Ejected parts trail — small parts that float upward in the background
  // Becomes visible after some parts have been "produced"
  const trailOpacity = interpolate(frame, [30, 90], [0, 0.4], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Generate a set of floating mini-parts for visual richness
  const miniParts = React.useMemo(() => {
    const parts: Array<{
      id: number;
      startFrame: number;
      x: number;
      speed: number;
      size: number;
    }> = [];
    for (let i = 0; i < 20; i++) {
      parts.push({
        id: i,
        startFrame: 30 + i * 12,
        x: 700 + ((i * 137) % 520), // pseudo-random x positions around mold center
        speed: 0.8 + ((i * 31) % 10) / 10, // varied speeds
        size: 10 + ((i * 17) % 20),
      });
    }
    return parts;
  }, []);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Background video — mold producing parts */}
      <AbsoluteFill style={{ opacity: videoOpacity }}>
        <OffthreadVideo
          src={staticFile("veo/mold_producing_parts.mp4")}
          style={{
            width: "100%",
            height: "100%",
            objectFit: "cover",
          }}
          muted
        />
      </AbsoluteFill>

      {/* Dark overlay for contrast */}
      <AbsoluteFill
        style={{
          background: `radial-gradient(ellipse at center, rgba(10,15,26,${0.55}) 0%, rgba(10,15,26,${vignetteIntensity}) 70%, rgba(10,15,26,0.92) 100%)`,
        }}
      />

      {/* Floating mini-parts trail */}
      {miniParts.map((part) => {
        if (frame < part.startFrame) return null;
        const elapsed = frame - part.startFrame;
        const y = 440 - elapsed * part.speed * 2;
        const partOpacity = interpolate(
          elapsed,
          [0, 10, 60, 80],
          [0, trailOpacity * 0.6, trailOpacity * 0.4, 0],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }
        );
        if (partOpacity <= 0 || y < -50) return null;
        return (
          <div
            key={part.id}
            style={{
              position: "absolute",
              left: part.x,
              top: y,
              width: part.size,
              height: part.size * 1.4,
              backgroundColor: "#D9944A",
              borderRadius: 3,
              opacity: partOpacity,
            }}
          />
        );
      })}

      {/* Mold cycle 2D animation */}
      <MoldCycleAnimation />

      {/* Exponential counter (lower-right) */}
      <ExponentialCounter />

      {/* Progress bar (beneath counter) */}
      <ProgressBar />

      {/* Horizontal divider above counter area */}
      <div
        style={{
          position: "absolute",
          left: 1270,
          top: 685,
          width: 360,
          height: 2,
          background: `linear-gradient(90deg, transparent, rgba(226,232,240,0.25), transparent)`,
          opacity: 0.8,
        }}
      />
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift04MoldProductionCounter;
