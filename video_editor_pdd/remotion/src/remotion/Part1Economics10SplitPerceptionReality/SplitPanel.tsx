import React from "react";
import { useCurrentFrame, interpolate, Easing, spring } from "remotion";
import { ArrowIcon } from "./ArrowIcon";
import { PanelIcon } from "./PanelIcon";
import {
  PANEL_TOP,
  PANEL_HEIGHT,
  LEFT_PANEL_X,
  LEFT_PANEL_WIDTH,
  RIGHT_PANEL_X,
  RIGHT_PANEL_WIDTH,
  PERCEPTION_COLOR,
  PERCEPTION_BG,
  PERCEPTION_MUTED,
  PERCEPTION_ICON_OPACITY,
  REALITY_COLOR,
  REALITY_BG,
  REALITY_MUTED,
  REALITY_ICON_OPACITY,
  STAT_COLOR,
  HEADER_FONT_SIZE,
  HEADER_LETTER_SPACING,
  STAT_FONT_SIZE,
  DESCRIPTOR_FONT_SIZE,
  PERCEPTION_STAT_VALUE,
  PERCEPTION_STAT_PREFIX,
  PERCEPTION_STAT_SUFFIX,
  PERCEPTION_DESCRIPTOR,
  REALITY_STAT_VALUE,
  REALITY_STAT_SUFFIX,
  REALITY_DESCRIPTOR,
  PANEL_SLIDE_IN_START,
  PANEL_SLIDE_IN_END,
  LEFT_HEADER_START,
  LEFT_HEADER_END,
  LEFT_STAT_START,
  LEFT_STAT_END,
  RIGHT_HEADER_START,
  RIGHT_HEADER_END,
  RIGHT_STAT_START,
  RIGHT_STAT_END,
  SLIDE_OUT_START,
  SLIDE_OUT_END,
  SLIDE_DISTANCE,
  SPRING_DAMPING,
  SPRING_STIFFNESS,
  FPS,
} from "./constants";

interface SplitPanelProps {
  side: "left" | "right";
}

export const SplitPanel: React.FC<SplitPanelProps> = ({ side }) => {
  const frame = useCurrentFrame();
  const isLeft = side === "left";

  // Panel config
  const panelX = isLeft ? LEFT_PANEL_X : RIGHT_PANEL_X;
  const panelWidth = isLeft ? LEFT_PANEL_WIDTH : RIGHT_PANEL_WIDTH;
  const bgColor = isLeft ? PERCEPTION_BG : REALITY_BG;
  const accentColor = isLeft ? PERCEPTION_COLOR : REALITY_COLOR;
  const mutedColor = isLeft ? PERCEPTION_MUTED : REALITY_MUTED;
  const headerText = isLeft ? "PERCEPTION" : "REALITY";
  const statValue = isLeft ? PERCEPTION_STAT_VALUE : REALITY_STAT_VALUE;
  const statPrefix = isLeft ? PERCEPTION_STAT_PREFIX : "";
  const statSuffix = isLeft ? PERCEPTION_STAT_SUFFIX : REALITY_STAT_SUFFIX;
  const descriptor = isLeft ? PERCEPTION_DESCRIPTOR : REALITY_DESCRIPTOR;
  const arrowDirection = isLeft ? "up" as const : "down" as const;
  const iconType = isLeft ? "thumbsUp" as const : "stopwatch" as const;
  const iconOpacity = isLeft ? PERCEPTION_ICON_OPACITY : REALITY_ICON_OPACITY;

  // Animation timing
  const headerStart = isLeft ? LEFT_HEADER_START : RIGHT_HEADER_START;
  const headerEnd = isLeft ? LEFT_HEADER_END : RIGHT_HEADER_END;
  const statStart = isLeft ? LEFT_STAT_START : RIGHT_STAT_START;
  const statEnd = isLeft ? LEFT_STAT_END : RIGHT_STAT_END;

  // Panel slide in using spring
  const slideInSpring = spring({
    frame: frame - PANEL_SLIDE_IN_START,
    fps: FPS,
    config: { damping: SPRING_DAMPING, stiffness: SPRING_STIFFNESS },
  });
  const slideInX = isLeft
    ? interpolate(slideInSpring, [0, 1], [-SLIDE_DISTANCE, 0])
    : interpolate(slideInSpring, [0, 1], [SLIDE_DISTANCE, 0]);

  // Panel slide out using easeInCubic
  const slideOutProgress = interpolate(
    frame,
    [SLIDE_OUT_START, SLIDE_OUT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.cubic) }
  );
  const slideOutX = isLeft
    ? interpolate(slideOutProgress, [0, 1], [0, -SLIDE_DISTANCE])
    : interpolate(slideOutProgress, [0, 1], [0, SLIDE_DISTANCE]);

  const translateX = frame < SLIDE_OUT_START ? slideInX : slideOutX;

  // Opacity
  const opacityIn = interpolate(
    frame,
    [PANEL_SLIDE_IN_START, PANEL_SLIDE_IN_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const opacityOut = interpolate(
    frame,
    [SLIDE_OUT_START, SLIDE_OUT_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const panelOpacity = Math.min(opacityIn, opacityOut);

  // Header + arrow fade in
  const headerOpacity = interpolate(
    frame,
    [headerStart, headerEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Stat counter animation
  const counterRaw = interpolate(
    frame,
    [statStart, statEnd],
    [0, statValue],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );
  const counterDisplay = Math.round(counterRaw);

  // Stat scale (0.8 → 1.0)
  const statScale = interpolate(
    frame,
    [statStart, statEnd],
    [0.8, 1.0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Descriptor fades in slightly after stat starts
  const descriptorOpacity = interpolate(
    frame,
    [statStart + 5, statEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: panelX,
        top: PANEL_TOP,
        width: panelWidth,
        height: PANEL_HEIGHT,
        backgroundColor: bgColor,
        transform: `translateX(${translateX}px)`,
        opacity: panelOpacity,
        overflow: "hidden",
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "center",
        gap: 20,
      }}
    >
      {/* Background icon silhouette */}
      <div
        style={{
          position: "absolute",
          bottom: 60,
          right: isLeft ? 60 : undefined,
          left: isLeft ? undefined : 60,
        }}
      >
        <PanelIcon type={iconType} color={accentColor} opacity={iconOpacity} />
      </div>

      {/* Header */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 900,
          fontSize: HEADER_FONT_SIZE,
          letterSpacing: HEADER_LETTER_SPACING,
          color: accentColor,
          textTransform: "uppercase" as const,
          opacity: headerOpacity,
        }}
      >
        {headerText}
      </div>

      {/* Arrow */}
      <div style={{ opacity: headerOpacity }}>
        <ArrowIcon direction={arrowDirection} color={accentColor} />
      </div>

      {/* Stat number */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 900,
          fontSize: STAT_FONT_SIZE,
          color: STAT_COLOR,
          lineHeight: 1,
          transform: `scale(${statScale})`,
        }}
      >
        {statPrefix}{counterDisplay}{statSuffix}
      </div>

      {/* Descriptor */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 500,
          fontSize: DESCRIPTOR_FONT_SIZE,
          color: mutedColor,
          opacity: descriptorOpacity,
        }}
      >
        {descriptor}
      </div>
    </div>
  );
};

export default SplitPanel;
