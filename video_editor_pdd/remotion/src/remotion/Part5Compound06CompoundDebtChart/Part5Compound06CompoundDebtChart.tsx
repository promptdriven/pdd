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
import {
  BG_COLOR,
  PATCHING_COLOR,
  GENERATION_COLOR,
  PATCHING_LINE_WIDTH,
  GENERATION_LINE_WIDTH,
  PATCHING_POINTS,
  GENERATION_POINTS,
  CURVES_DRAW_START,
  CURVES_DRAW_DURATION,
  GAP_FILL_START,
  GAP_FILL_END,
  ANNOTATION_FADE_START,
  ANNOTATION_X,
  ANNOTATION_Y,
  FADEOUT_START,
  FADEOUT_END,
  TOTAL_FRAMES,
} from "./constants";

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
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part5_compound.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Chart overlay with master fade-out */}
      <AbsoluteFill style={{ opacity: masterOpacity }}>
        {/* Phase 1-2: Axes, grid, and time markers fade in (frame 0-50) */}
        <ChartAxes />

        {/* Phase 4: Patching curve — exponential climb (frame 45 onward) */}
        <Sequence from={CURVES_DRAW_START} durationInFrames={TOTAL_FRAMES - CURVES_DRAW_START}>
          <AnimatedCurve
            points={PATCHING_POINTS}
            stroke={PATCHING_COLOR}
            strokeWidth={PATCHING_LINE_WIDTH}
            drawStartFrame={0}
            drawEndFrame={CURVES_DRAW_DURATION}
            label="Patching"
            smooth
          />
        </Sequence>

        {/* Phase 4: Generation curve — flat with sawtooth resets (frame 45 onward) */}
        <Sequence from={CURVES_DRAW_START} durationInFrames={TOTAL_FRAMES - CURVES_DRAW_START}>
          <AnimatedCurve
            points={GENERATION_POINTS}
            stroke={GENERATION_COLOR}
            strokeWidth={GENERATION_LINE_WIDTH}
            drawStartFrame={0}
            drawEndFrame={CURVES_DRAW_DURATION}
            label="Generation"
            smooth={false}
          />
        </Sequence>

        {/* Phase 5: Gap fill between curves (frame 100 onward) */}
        <Sequence from={GAP_FILL_START} durationInFrames={TOTAL_FRAMES - GAP_FILL_START}>
          <GapFill
            topCurve={PATCHING_POINTS}
            bottomCurve={GENERATION_POINTS}
            fillStartFrame={0}
            fillEndFrame={GAP_FILL_END - GAP_FILL_START}
          />
        </Sequence>

        {/* Phase 6: Gap annotation (frame 300 onward) */}
        <Sequence from={ANNOTATION_FADE_START} durationInFrames={TOTAL_FRAMES - ANNOTATION_FADE_START}>
          <GapAnnotation
            text="The gap compounds"
            x={ANNOTATION_X}
            y={ANNOTATION_Y}
            fadeInStart={0}
            fadeInEnd={50}
            fadeOutStart={TOTAL_FRAMES}
            fadeOutEnd={TOTAL_FRAMES}
          />
        </Sequence>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part5Compound06CompoundDebtChart;
