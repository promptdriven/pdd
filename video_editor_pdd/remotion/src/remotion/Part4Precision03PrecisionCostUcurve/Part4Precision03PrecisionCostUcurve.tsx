import React from "react";
import {
  AbsoluteFill,
  Easing,
  interpolate,
  OffthreadVideo,
  spring,
  staticFile,
  useCurrentFrame,
  useVideoConfig,
} from "remotion";
import { ChartAxes } from "./ChartAxes";
import { DangerZone } from "./DangerZone";
import { AnimatedCurve } from "./AnimatedCurve";
import { SweetSpot } from "./SweetSpot";
import {
  BG_COLOR,
  RED,
  AMBER,
  AXES_FADE_START,
  AXES_FADE_END,
  GRID_FADE_START,
  GRID_FADE_END,
  LEFT_DANGER_FADE_START,
  LEFT_DANGER_FADE_END,
  RIGHT_DANGER_FADE_START,
  RIGHT_DANGER_FADE_END,
  CURVE_DRAW_START,
  CURVE_DRAW_END,
  SWEET_DOT_START,
  SWEET_LABEL_START,
  SWEET_LABEL_END,
  CHART_FADE_OUT_START,
  CHART_FADE_OUT_END,
  TOTAL_FRAMES,
} from "./constants";

export const defaultPart4Precision03PrecisionCostUcurveProps = {};

export const Part4Precision03PrecisionCostUcurve: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Overall chart fade out
  const chartFadeOut = interpolate(
    frame,
    [CHART_FADE_OUT_START, CHART_FADE_OUT_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.cubic) }
  );

  // Axes fade in
  const axisOpacity =
    interpolate(
      frame,
      [AXES_FADE_START, AXES_FADE_END],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
    ) * chartFadeOut;

  // Grid fade in
  const gridOpacity =
    interpolate(
      frame,
      [GRID_FADE_START, GRID_FADE_END],
      [0, 0.15],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    ) * chartFadeOut;

  // Left danger zone
  const leftZoneOpacity =
    interpolate(
      frame,
      [LEFT_DANGER_FADE_START, LEFT_DANGER_FADE_END],
      [0, 0.08],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
    ) * chartFadeOut;
  const leftLabelOpacity =
    interpolate(
      frame,
      [LEFT_DANGER_FADE_START, LEFT_DANGER_FADE_END],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
    ) * chartFadeOut;

  // Right danger zone
  const rightZoneOpacity =
    interpolate(
      frame,
      [RIGHT_DANGER_FADE_START, RIGHT_DANGER_FADE_END],
      [0, 0.08],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
    ) * chartFadeOut;
  const rightLabelOpacity =
    interpolate(
      frame,
      [RIGHT_DANGER_FADE_START, RIGHT_DANGER_FADE_END],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
    ) * chartFadeOut;

  // U-curve draw progress
  const curveDrawProgress = interpolate(
    frame,
    [CURVE_DRAW_START, CURVE_DRAW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.quad) }
  );
  const curveOpacity =
    interpolate(
      frame,
      [CURVE_DRAW_START, CURVE_DRAW_START + 1],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    ) * chartFadeOut;

  // Sweet spot dot — spring scale
  const dotScale =
    frame >= SWEET_DOT_START
      ? spring({
          frame: frame - SWEET_DOT_START,
          fps,
          config: { damping: 12, stiffness: 200 },
        })
      : 0;

  // Sweet spot glow — sinusoidal pulse, 2s period (60 frames at 30fps)
  const glowOpacity =
    frame >= SWEET_DOT_START
      ? interpolate(
          Math.sin(((frame - SWEET_DOT_START) * Math.PI * 2) / 60),
          [-1, 1],
          [0.4, 0.8]
        )
      : 0;

  // Sweet spot label
  const sweetLabelOpacity =
    interpolate(
      frame,
      [SWEET_LABEL_START, SWEET_LABEL_END],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    ) * chartFadeOut;

  // Sweet spot overall opacity (for fade out)
  const sweetOverallOpacity =
    frame >= SWEET_DOT_START ? chartFadeOut : 0;

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part4_precision.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Axes and grid — visible from frame 0 */}
      <ChartAxes axisOpacity={axisOpacity} gridOpacity={gridOpacity} />

      {/* Left danger zone */}
      <DangerZone
        side="left"
        label="AI Hallucinates"
        color={RED}
        zoneOpacity={leftZoneOpacity}
        labelOpacity={leftLabelOpacity}
      />

      {/* Right danger zone */}
      <DangerZone
        side="right"
        label="Writing Code Yourself"
        color={AMBER}
        zoneOpacity={rightZoneOpacity}
        labelOpacity={rightLabelOpacity}
      />

      {/* U-Curve */}
      <AnimatedCurve
        drawProgress={curveDrawProgress}
        opacity={curveOpacity}
      />

      {/* Sweet spot */}
      <SweetSpot
        dotScale={dotScale}
        glowOpacity={glowOpacity}
        labelOpacity={sweetLabelOpacity}
        overallOpacity={sweetOverallOpacity}
      />
    </AbsoluteFill>
  );
};

export default Part4Precision03PrecisionCostUcurve;
