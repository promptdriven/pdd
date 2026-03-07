import React from "react";
import {
  AbsoluteFill,
  Easing,
  interpolate,
  OffthreadVideo,
  Sequence,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { ChartAxes } from "./ChartAxes";
import { AnimatedCurve } from "./AnimatedCurve";
import { GapFill } from "./GapFill";
import { GapAnnotation } from "./GapAnnotation";
import {
  PATCHING_POINTS,
  GENERATION_POINTS,
  PATCHING_COLOR,
  GENERATION_COLOR,
  PATCHING_LINE_WIDTH,
  GENERATION_LINE_WIDTH,
  CURVES_DRAW_START,
  CURVES_DRAW_END,
  GAP_FILL_START,
  GAP_FILL_END,
  ANNOTATION_FADE_START,
  ANNOTATION_FADE_END,
  ANNOTATION_X,
  ANNOTATION_Y,
  FADEOUT_START,
  FADEOUT_END,
  TOTAL_FRAMES,
} from "./constants";

export const defaultPart5Compound06CompoundDebtChartProps = {};

export const Part5Compound06CompoundDebtChart: React.FC = () => {
  const frame = useCurrentFrame();

  // Global fade out for the entire chart overlay (Phase 8: 600-660)
  const globalOpacity = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    },
  );

  return (
    <AbsoluteFill style={{ backgroundColor: "#0A1628" }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part5_compound.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover", opacity: 0.3 }}
          muted
        />
      </AbsoluteFill>

      {/* Chart overlay — fades out at end */}
      <AbsoluteFill style={{ opacity: globalOpacity }}>
        {/* Axes, grid, labels — visible from frame 0 */}
        <ChartAxes />

        {/* Patching curve — exponential climb */}
        <Sequence from={CURVES_DRAW_START} durationInFrames={TOTAL_FRAMES - CURVES_DRAW_START}>
          <AnimatedCurve
            points={PATCHING_POINTS}
            color={PATCHING_COLOR}
            strokeWidth={PATCHING_LINE_WIDTH}
            drawStartFrame={0}
            drawEndFrame={CURVES_DRAW_END - CURVES_DRAW_START}
            label="Patching"
            smooth
            fadeOutStart={FADEOUT_START - CURVES_DRAW_START}
            fadeOutEnd={FADEOUT_END - CURVES_DRAW_START}
          />
        </Sequence>

        {/* Generation curve — flat with sawtooth resets */}
        <Sequence from={CURVES_DRAW_START} durationInFrames={TOTAL_FRAMES - CURVES_DRAW_START}>
          <AnimatedCurve
            points={GENERATION_POINTS}
            color={GENERATION_COLOR}
            strokeWidth={GENERATION_LINE_WIDTH}
            drawStartFrame={0}
            drawEndFrame={CURVES_DRAW_END - CURVES_DRAW_START}
            label="Generation"
            smooth={false}
            fadeOutStart={FADEOUT_START - CURVES_DRAW_START}
            fadeOutEnd={FADEOUT_END - CURVES_DRAW_START}
          />
        </Sequence>

        {/* Gap fill between curves */}
        <Sequence from={GAP_FILL_START} durationInFrames={TOTAL_FRAMES - GAP_FILL_START}>
          <GapFill
            topCurve={PATCHING_POINTS}
            bottomCurve={GENERATION_POINTS}
            fillStartFrame={0}
            fillEndFrame={GAP_FILL_END - GAP_FILL_START}
            fadeOutStart={FADEOUT_START - GAP_FILL_START}
            fadeOutEnd={FADEOUT_END - GAP_FILL_START}
          />
        </Sequence>

        {/* Gap annotation — "The gap compounds" + arrow */}
        <Sequence from={ANNOTATION_FADE_START} durationInFrames={TOTAL_FRAMES - ANNOTATION_FADE_START}>
          <GapAnnotation
            x={ANNOTATION_X}
            y={ANNOTATION_Y}
            fadeInStart={0}
            fadeInEnd={ANNOTATION_FADE_END - ANNOTATION_FADE_START}
            fadeOutStart={FADEOUT_START - ANNOTATION_FADE_START}
            fadeOutEnd={FADEOUT_END - ANNOTATION_FADE_START}
          />
        </Sequence>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part5Compound06CompoundDebtChart;
