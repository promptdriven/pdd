import React from "react";
import {
  AbsoluteFill,
  Sequence,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { ChartAxes } from "./ChartAxes";
import { AnimatedCurve } from "./AnimatedCurve";
import { GapFill } from "./GapFill";
import { GapAnnotation } from "./GapAnnotation";

// Patching curve: exponential growth (normalized 0-1)
const PATCHING_POINTS = [
  { x: 0, y: 0.02 },
  { x: 0.087, y: 0.06 },
  { x: 0.217, y: 0.15 },
  { x: 0.348, y: 0.30 },
  { x: 0.478, y: 0.50 },
  { x: 0.609, y: 0.68 },
  { x: 0.739, y: 0.82 },
  { x: 0.870, y: 0.91 },
  { x: 1.0, y: 0.97 },
];

// Generation curve: flat with sawtooth resets (normalized 0-1)
const GENERATION_POINTS = [
  { x: 0, y: 0.02 },
  { x: 0.130, y: 0.05 },
  { x: 0.174, y: 0.01 },
  { x: 0.304, y: 0.05 },
  { x: 0.348, y: 0.01 },
  { x: 0.478, y: 0.05 },
  { x: 0.522, y: 0.01 },
  { x: 0.652, y: 0.05 },
  { x: 0.696, y: 0.01 },
  { x: 0.826, y: 0.05 },
  { x: 0.870, y: 0.01 },
  { x: 1.0, y: 0.04 },
];

// Frame constants
const FADEOUT_START = 600;
const FADEOUT_END = 660;

export const defaultPart5Compound06CompoundDebtChartProps = {};

export const Part5Compound06CompoundDebtChart: React.FC = () => {
  const frame = useCurrentFrame();

  // Master fade-out for the entire chart (frames 600-660)
  const masterOpacity = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: "#0A1628" }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part5_compound.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Chart overlay */}
      <AbsoluteFill style={{ opacity: masterOpacity }}>
        {/* Phase 1-2: Axes, grid, and time markers fade in (frame 0-50) */}
        <ChartAxes masterOpacity={1} />

        {/* Phase 4: Patching curve — exponential climb (frame 45-350) */}
        <Sequence from={45} durationInFrames={615}>
          <AnimatedCurve
            points={PATCHING_POINTS}
            stroke="#EF4444"
            strokeWidth={4}
            drawStartFrame={0}
            drawEndFrame={305}
            fadeOutStart={555}
            fadeOutEnd={615}
            label="Patching"
            smooth
          />
        </Sequence>

        {/* Phase 4: Generation curve — flat with sawtooth resets (frame 45-350) */}
        <Sequence from={45} durationInFrames={615}>
          <AnimatedCurve
            points={GENERATION_POINTS}
            stroke="#22C55E"
            strokeWidth={3}
            drawStartFrame={0}
            drawEndFrame={305}
            fadeOutStart={555}
            fadeOutEnd={615}
            label="Generation"
            smooth={false}
          />
        </Sequence>

        {/* Phase 5: Gap fill between curves (frame 100-350) */}
        <Sequence from={100} durationInFrames={560}>
          <GapFill
            topCurve={PATCHING_POINTS}
            bottomCurve={GENERATION_POINTS}
            fillStartFrame={0}
            fillEndFrame={250}
            fadeOutStart={500}
            fadeOutEnd={560}
          />
        </Sequence>

        {/* Phase 6: Gap annotation (frame 300-660) */}
        <Sequence from={300} durationInFrames={360}>
          <GapAnnotation
            text="The gap compounds"
            x={1200}
            y={400}
            fadeInStart={0}
            fadeInEnd={50}
            fadeOutStart={300}
            fadeOutEnd={360}
          />
        </Sequence>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part5Compound06CompoundDebtChart;
