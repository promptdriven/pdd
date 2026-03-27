// Part3MoldParts16ThreeComponentsPullback.tsx
// Section 3.16 — Pull back to see all three mold components working as a unified pipeline.
// Duration: 270 frames (9s @ 30fps)

import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BACKGROUND_COLOR,
  STAGES,
  MOLD_LEFT,
  MOLD_WIDTH,
} from "./constants";
import { BlueprintGrid } from "./BlueprintGrid";
import { MoldCrossSection } from "./MoldCrossSection";
import { ParticleFlow } from "./ParticleFlow";
import { FlowLabel } from "./FlowLabel";

export const defaultPart3MoldParts16ThreeComponentsPullbackProps = {};

export const Part3MoldParts16ThreeComponentsPullback: React.FC = () => {
  const frame = useCurrentFrame();

  // Subtle scale animation: starts slightly zoomed in, pulls back to 1.0
  const scale = interpolate(frame, [0, 60], [1.05, 1.0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Title text at top — "Complete Pipeline" fades in mid-sequence
  const titleOpacity = interpolate(frame, [120, 140], [0, 0.85], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Blueprint grid background */}
      <BlueprintGrid />

      {/* Scaled container for pullback effect */}
      <AbsoluteFill
        style={{
          transform: `scale(${scale})`,
          transformOrigin: "center center",
        }}
      >
        {/* Mold cross-section — fades in from frame 0 */}
        <MoldCrossSection />

        {/* Particle flow animation — starts at frame 30 */}
        <ParticleFlow />

        {/* Flow labels — SVG overlay */}
        <svg
          width={1920}
          height={1080}
          style={{ position: "absolute", top: 0, left: 0 }}
        >
          {STAGES.map((stage, i) => {
            // Compute connecting line endpoint
            const lineToX =
              stage.labelX < 960
                ? MOLD_LEFT - 10
                : MOLD_LEFT + MOLD_WIDTH + 10;

            return (
              <FlowLabel
                key={stage.encodes}
                text={stage.encodes}
                color={stage.color}
                x={stage.labelX}
                y={stage.labelY}
                appearFrame={stage.flowStartFrame}
                lineToX={lineToX}
              />
            );
          })}
        </svg>
      </AbsoluteFill>

      {/* Title overlay */}
      <div
        style={{
          position: "absolute",
          top: 50,
          left: 0,
          width: "100%",
          display: "flex",
          justifyContent: "center",
          opacity: titleOpacity,
        }}
      >
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 28,
            fontWeight: 700,
            color: "#E2E8F0",
            letterSpacing: "0.05em",
            textTransform: "uppercase",
          }}
        >
          Complete Pipeline
        </div>
      </div>

      {/* Bottom summary labels — stage components with arrows */}
      <div
        style={{
          position: "absolute",
          bottom: 60,
          left: 0,
          width: "100%",
          display: "flex",
          justifyContent: "center",
          gap: 16,
          alignItems: "center",
          opacity: interpolate(frame, [140, 165], [0, 0.9], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }),
        }}
      >
        {STAGES.map((stage, i) => (
          <React.Fragment key={stage.component}>
            <div
              style={{
                fontFamily: "Inter, sans-serif",
                fontSize: 18,
                fontWeight: 600,
                color: stage.color,
                opacity: 0.85,
              }}
            >
              {stage.component}
            </div>
            {i < STAGES.length - 1 && (
              <div
                style={{
                  fontFamily: "Inter, sans-serif",
                  fontSize: 18,
                  color: "#475569",
                  opacity: 0.8,
                }}
              >
                {"\u2192"}
              </div>
            )}
          </React.Fragment>
        ))}
      </div>
    </AbsoluteFill>
  );
};

export default Part3MoldParts16ThreeComponentsPullback;
