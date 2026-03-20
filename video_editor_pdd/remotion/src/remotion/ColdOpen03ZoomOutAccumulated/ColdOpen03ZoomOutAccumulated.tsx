import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate } from "remotion";
import "../_shared/load-inter-font";
import {
  BG_LEFT,
  BG_RIGHT,
  DIVIDER_COLOR,
  DIVIDER_OPACITY,
  DIVIDER_WIDTH,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  SPLIT_X,
  PANEL_WIDTH,
  LEFT_COUNTER_COLOR,
  RIGHT_COUNTER_COLOR,
  LEFT_COUNTER_TARGET,
  RIGHT_COUNTER_TARGET,
  PULSE_START,
  PULSE_DURATION,
} from "./constants";
import { CodebaseGrid } from "./CodebaseGrid";
import { DresserDrawer } from "./DresserDrawer";
import { AnimatedCounter } from "./AnimatedCounter";

export const defaultColdOpen03ZoomOutAccumulatedProps = {};

export const ColdOpen03ZoomOutAccumulated: React.FC = () => {
  const frame = useCurrentFrame();

  // Subtle brightness pulse at the end (frames 180-210) applied to full canvas
  const pulseProgress = interpolate(
    frame,
    [PULSE_START, PULSE_START + PULSE_DURATION],
    [0, Math.PI * 2],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const brightnessOffset =
    frame >= PULSE_START ? Math.sin(pulseProgress) * 0.02 : 0;
  const brightness = 1 + brightnessOffset;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#0A1628",
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        overflow: "hidden",
      }}
    >
      {/* LEFT PANEL — Codebase Sprawl */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: PANEL_WIDTH,
          height: CANVAS_HEIGHT,
          backgroundColor: BG_LEFT,
          overflow: "hidden",
          filter: `brightness(${brightness})`,
        }}
      >
        <CodebaseGrid />
        <AnimatedCounter
          targetValue={LEFT_COUNTER_TARGET}
          suffix="patches"
          color={LEFT_COUNTER_COLOR}
          align="left"
        />
      </div>

      {/* RIGHT PANEL — Mended Garments */}
      <div
        style={{
          position: "absolute",
          left: SPLIT_X,
          top: 0,
          width: PANEL_WIDTH,
          height: CANVAS_HEIGHT,
          backgroundColor: BG_RIGHT,
          overflow: "hidden",
          filter: `brightness(${brightness})`,
        }}
      >
        <DresserDrawer />
        <AnimatedCounter
          targetValue={RIGHT_COUNTER_TARGET}
          suffix="mended garments"
          color={RIGHT_COUNTER_COLOR}
          align="right"
        />
      </div>

      {/* SPLIT DIVIDER */}
      <div
        style={{
          position: "absolute",
          left: SPLIT_X - DIVIDER_WIDTH / 2,
          top: 0,
          width: DIVIDER_WIDTH,
          height: CANVAS_HEIGHT,
          backgroundColor: DIVIDER_COLOR,
          opacity: DIVIDER_OPACITY,
          zIndex: 10,
        }}
      />
    </AbsoluteFill>
  );
};

export default ColdOpen03ZoomOutAccumulated;
