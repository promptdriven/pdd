import React from "react";
import { useCurrentFrame, interpolate, Easing, spring } from "remotion";
import { DiffIcon } from "./DiffIcon";
import { RefreshCycleIcon } from "./RefreshCycleIcon";
import { MiniTimeline } from "./MiniTimeline";
import {
  PANEL_TOP,
  PANEL_HEIGHT,
  LEFT_PANEL_X,
  LEFT_PANEL_WIDTH,
  RIGHT_PANEL_X,
  RIGHT_PANEL_WIDTH,
  PATCHING_COLOR,
  PATCHING_BG,
  PATCHING_ICON_OPACITY,
  GENERATION_COLOR,
  GENERATION_BG,
  GENERATION_ICON_OPACITY,
  LABEL_COLOR,
  HEADER_FONT_SIZE,
  HEADER_LETTER_SPACING,
  TIMELINE_LABEL_FONT_SIZE,
  OUTCOME_FONT_SIZE,
  ICON_SIZE,
  PATCHING_HEADER,
  GENERATION_HEADER,
  PATCHING_TIMELINE_LABEL,
  GENERATION_TIMELINE_LABEL,
  PATCHING_OUTCOME,
  GENERATION_OUTCOME,
  PANEL_SLIDE_IN_START,
  PANEL_SLIDE_IN_END,
  LEFT_HEADER_START,
  LEFT_HEADER_END,
  LEFT_TIMELINE_START,
  LEFT_TIMELINE_END,
  RIGHT_HEADER_START,
  RIGHT_HEADER_END,
  RIGHT_TIMELINE_START,
  RIGHT_TIMELINE_END,
  OUTCOME_FADE_START,
  OUTCOME_FADE_END,
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
  const bgColor = isLeft ? PATCHING_BG : GENERATION_BG;
  const accentColor = isLeft ? PATCHING_COLOR : GENERATION_COLOR;
  const headerText = isLeft ? PATCHING_HEADER : GENERATION_HEADER;
  const timelineLabel = isLeft ? PATCHING_TIMELINE_LABEL : GENERATION_TIMELINE_LABEL;
  const outcomeText = isLeft ? PATCHING_OUTCOME : GENERATION_OUTCOME;
  const iconOpacity = isLeft ? PATCHING_ICON_OPACITY : GENERATION_ICON_OPACITY;
  const timelineType = isLeft ? ("rising_bars" as const) : ("flat_sawtooth" as const);

  // Animation timing
  const headerStart = isLeft ? LEFT_HEADER_START : RIGHT_HEADER_START;
  const headerEnd = isLeft ? LEFT_HEADER_END : RIGHT_HEADER_END;
  const timelineStart = isLeft ? LEFT_TIMELINE_START : RIGHT_TIMELINE_START;
  const timelineEnd = isLeft ? LEFT_TIMELINE_END : RIGHT_TIMELINE_END;

  // Panel slide in using spring
  const slideInSpring = spring({
    frame: frame - PANEL_SLIDE_IN_START,
    fps: FPS,
    config: { damping: SPRING_DAMPING, stiffness: SPRING_STIFFNESS },
  });
  const slideInX = isLeft
    ? interpolate(slideInSpring, [0, 1], [-SLIDE_DISTANCE, 0])
    : interpolate(slideInSpring, [0, 1], [SLIDE_DISTANCE, 0]);

  // Panel slide out
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

  // Header + icon fade in
  const headerOpacity = interpolate(
    frame,
    [headerStart, headerEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Outcome labels
  const outcomeOpacity = interpolate(
    frame,
    [OUTCOME_FADE_START, OUTCOME_FADE_END],
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
        justifyContent: "flex-start",
        paddingTop: 60,
        gap: 28,
      }}
    >
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

      {/* Icon */}
      <div style={{ opacity: headerOpacity }}>
        {isLeft ? (
          <DiffIcon color={accentColor} size={ICON_SIZE} opacity={iconOpacity} />
        ) : (
          <RefreshCycleIcon color={accentColor} size={ICON_SIZE} opacity={iconOpacity} />
        )}
      </div>

      {/* Mini timeline chart */}
      <div style={{ marginTop: 20 }}>
        <MiniTimeline
          type={timelineType}
          color={accentColor}
          animateStart={timelineStart}
          animateEnd={timelineEnd}
        />
      </div>

      {/* Timeline label */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 500,
          fontSize: TIMELINE_LABEL_FONT_SIZE,
          color: LABEL_COLOR,
          opacity: interpolate(
            frame,
            [timelineStart + 10, timelineEnd + 5],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
          ),
        }}
      >
        {timelineLabel}
      </div>

      {/* Outcome text */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 700,
          fontSize: OUTCOME_FONT_SIZE,
          color: accentColor,
          opacity: outcomeOpacity,
          marginTop: 24,
        }}
      >
        {outcomeText}
      </div>
    </div>
  );
};

export default SplitPanel;
