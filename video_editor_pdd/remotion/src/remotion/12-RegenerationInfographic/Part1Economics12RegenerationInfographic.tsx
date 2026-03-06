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
import { DocIcon } from "./DocIcon";
import { ExpandingArrow } from "./ExpandingArrow";
import { ChartAxes } from "./ChartAxes";
import { UCurve } from "./UCurve";
import { SweetSpotMarker } from "./SweetSpotMarker";
import { CalloutBadge } from "./CalloutBadge";
import {
  BG_COLOR,
  BLUE,
  GREEN,
  SMALL_DOC_POS,
  SMALL_DOC_SIZE,
  LARGE_DOC_POS,
  LARGE_DOC_SIZE,
  ARROW_FROM,
  ARROW_TO,
  SMALL_DOC_FADE_START,
  SMALL_DOC_FADE_END,
  ARROW_DRAW_START,
  ARROW_DRAW_END,
  LARGE_DOC_FADE_START,
  LARGE_DOC_FADE_END,
  LABELS_FADE_START,
  LABELS_FADE_END,
  AXES_FADE_START,
  AXES_FADE_END,
  CURVE_DRAW_START,
  CURVE_DRAW_END,
  SWEET_SPOT_START,
  BADGE_SLIDE_START,
  BADGE_SLIDE_END,
} from "./constants";

export const defaultPart1Economics12RegenerationInfographicProps = {};

export const Part1Economics12RegenerationInfographic: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  const clamp = { extrapolateLeft: "clamp" as const, extrapolateRight: "clamp" as const };

  // --- Part A: Compression Ratio ---

  // Small doc icon — scale and opacity
  const smallDocScale =
    frame >= SMALL_DOC_FADE_START
      ? spring({
          frame: frame - SMALL_DOC_FADE_START,
          fps,
          config: { damping: 12, stiffness: 180 },
        })
      : 0;
  const smallDocOpacity = interpolate(
    frame,
    [SMALL_DOC_FADE_START, SMALL_DOC_FADE_START + 15],
    [0, 1],
    clamp
  );

  // Expanding arrow — draw progress
  const arrowProgress = interpolate(
    frame,
    [ARROW_DRAW_START, ARROW_DRAW_END],
    [0, 1],
    { ...clamp, easing: Easing.inOut(Easing.quad) }
  );
  const arrowOpacity = interpolate(
    frame,
    [ARROW_DRAW_START, ARROW_DRAW_START + 5],
    [0, 1],
    clamp
  );

  // Large doc icon — scale and opacity
  const largeDocScale =
    frame >= LARGE_DOC_FADE_START
      ? spring({
          frame: frame - LARGE_DOC_FADE_START,
          fps,
          config: { damping: 12, stiffness: 180 },
        })
      : 0;
  const largeDocOpacity = interpolate(
    frame,
    [LARGE_DOC_FADE_START, LARGE_DOC_FADE_START + 15],
    [0, 1],
    clamp
  );

  // "5-10x expansion" label appears with large doc
  const expansionLabelOpacity = interpolate(
    frame,
    [LARGE_DOC_FADE_START + 10, LARGE_DOC_FADE_END],
    [0, 1],
    clamp
  );

  // Doc sublabels fade in
  const labelOpacity = interpolate(
    frame,
    [LABELS_FADE_START, LABELS_FADE_END],
    [0, 1],
    clamp
  );

  // --- Part B: U-Curve ---

  // Axes fade in
  const axesOpacity = interpolate(
    frame,
    [AXES_FADE_START, AXES_FADE_END],
    [0, 1],
    { ...clamp, easing: Easing.out(Easing.cubic) }
  );

  // U-curve draw progress
  const curveDrawProgress = interpolate(
    frame,
    [CURVE_DRAW_START, CURVE_DRAW_END],
    [0, 1],
    { ...clamp, easing: Easing.inOut(Easing.cubic) }
  );
  const curveOpacity = interpolate(
    frame,
    [CURVE_DRAW_START, CURVE_DRAW_START + 1],
    [0, 1],
    clamp
  );

  // Sweet spot marker — spring
  const sweetSpotScale =
    frame >= SWEET_SPOT_START
      ? spring({
          frame: frame - SWEET_SPOT_START,
          fps,
          config: { damping: 10, stiffness: 200 },
        })
      : 0;
  const sweetSpotOpacity = frame >= SWEET_SPOT_START ? 1 : 0;

  // MIT callout badge — slide in from right
  const badgeTranslateX = interpolate(
    frame,
    [BADGE_SLIDE_START, BADGE_SLIDE_END],
    [100, 0],
    { ...clamp, easing: Easing.out(Easing.cubic) }
  );
  const badgeOpacity = interpolate(
    frame,
    [BADGE_SLIDE_START, BADGE_SLIDE_END],
    [0, 1],
    clamp
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part1_economics.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover", opacity: 0.3 }}
          muted
        />
      </AbsoluteFill>

      {/* Part A — Compression Ratio */}

      {/* Small doc icon (prompt) */}
      <DocIcon
        x={SMALL_DOC_POS.x}
        y={SMALL_DOC_POS.y}
        width={SMALL_DOC_SIZE.w}
        height={SMALL_DOC_SIZE.h}
        color={BLUE}
        label="Prompt"
        sublabel="~50 lines"
        scale={smallDocScale}
        opacity={smallDocOpacity}
        labelOpacity={labelOpacity}
      />

      {/* Expanding arrow */}
      <ExpandingArrow
        fromX={ARROW_FROM.x}
        fromY={ARROW_FROM.y}
        toX={ARROW_TO.x}
        toY={ARROW_TO.y}
        progress={arrowProgress}
        opacity={arrowOpacity}
        labelOpacity={expansionLabelOpacity}
      />

      {/* Large doc icon (generated module) */}
      <DocIcon
        x={LARGE_DOC_POS.x}
        y={LARGE_DOC_POS.y}
        width={LARGE_DOC_SIZE.w}
        height={LARGE_DOC_SIZE.h}
        color={GREEN}
        label="Generated Module"
        sublabel="~250-500 lines"
        scale={largeDocScale}
        opacity={largeDocOpacity}
        labelOpacity={labelOpacity}
        showCodeLines
      />

      {/* Part B — U-Curve */}

      {/* Chart axes */}
      <ChartAxes opacity={axesOpacity} />

      {/* Animated U-curve */}
      <UCurve
        drawProgress={curveDrawProgress}
        opacity={curveOpacity}
      />

      {/* Sweet spot marker */}
      <SweetSpotMarker
        scale={sweetSpotScale}
        opacity={sweetSpotOpacity}
      />

      {/* MIT callout badge */}
      <CalloutBadge
        translateX={badgeTranslateX}
        opacity={badgeOpacity}
      />
    </AbsoluteFill>
  );
};

export default Part1Economics12RegenerationInfographic;
