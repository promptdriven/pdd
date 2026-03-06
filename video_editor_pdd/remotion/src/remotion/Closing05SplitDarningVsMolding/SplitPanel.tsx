import React from "react";
import { useCurrentFrame, interpolate, Easing, spring } from "remotion";
import { NeedleIcon } from "./NeedleIcon";
import { MoldIcon } from "./MoldIcon";
import { CostCurve } from "./CostCurve";
import {
  PANEL_TOP,
  PANEL_HEIGHT,
  LEFT_PANEL_X,
  LEFT_PANEL_WIDTH,
  RIGHT_PANEL_X,
  RIGHT_PANEL_WIDTH,
  DARNING_COLOR,
  DARNING_BG,
  DARNING_ICON_OPACITY,
  MOLDING_COLOR,
  MOLDING_BG,
  MOLDING_ICON_OPACITY,
  HEADER_FONT_SIZE,
  HEADER_LETTER_SPACING,
  OUTCOME_FONT_SIZE,
  ICON_SIZE,
  SLIDE_DISTANCE,
  SPRING_DAMPING,
  SPRING_STIFFNESS,
  FPS,
  PANEL_SLIDE_IN_START,
  PANEL_SLIDE_IN_END,
  LEFT_HEADER_START,
  LEFT_HEADER_END,
  LEFT_CURVE_START,
  LEFT_CURVE_END,
  RIGHT_HEADER_START,
  RIGHT_HEADER_END,
  RIGHT_CURVE_START,
  RIGHT_CURVE_END,
  OUTCOME_START,
  OUTCOME_END,
  DISSOLVE_START,
  DISSOLVE_END,
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
  const bgColor = isLeft ? DARNING_BG : MOLDING_BG;
  const accentColor = isLeft ? DARNING_COLOR : MOLDING_COLOR;
  const headerText = isLeft ? "DARNING" : "MOLDING";
  const outcomeText = isLeft ? "FRAGILE" : "RESILIENT";
  const curveType = isLeft ? "exponential" as const : "flat" as const;
  const iconOpacity = isLeft ? DARNING_ICON_OPACITY : MOLDING_ICON_OPACITY;
  const curveStart = isLeft ? LEFT_CURVE_START : RIGHT_CURVE_START;
  const curveEnd = isLeft ? LEFT_CURVE_END : RIGHT_CURVE_END;

  // Animation timing
  const headerStart = isLeft ? LEFT_HEADER_START : RIGHT_HEADER_START;
  const headerEnd = isLeft ? LEFT_HEADER_END : RIGHT_HEADER_END;

  // Panel slide in using spring
  const slideInSpring = spring({
    frame: frame - PANEL_SLIDE_IN_START,
    fps: FPS,
    config: { damping: SPRING_DAMPING, stiffness: SPRING_STIFFNESS },
  });
  const slideInX = isLeft
    ? interpolate(slideInSpring, [0, 1], [-SLIDE_DISTANCE, 0])
    : interpolate(slideInSpring, [0, 1], [SLIDE_DISTANCE, 0]);

  // Panel dissolve out
  const slideOutProgress = interpolate(
    frame,
    [DISSOLVE_START, DISSOLVE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.cubic) }
  );
  const slideOutX = isLeft
    ? interpolate(slideOutProgress, [0, 1], [0, -SLIDE_DISTANCE])
    : interpolate(slideOutProgress, [0, 1], [0, SLIDE_DISTANCE]);

  const translateX = frame < DISSOLVE_START ? slideInX : slideOutX;

  // Opacity
  const opacityIn = interpolate(
    frame,
    [PANEL_SLIDE_IN_START, PANEL_SLIDE_IN_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const opacityOut = interpolate(
    frame,
    [DISSOLVE_START, DISSOLVE_END],
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

  // Outcome word scale + opacity (easeOutBack approximation via poly)
  const outcomeOpacity = interpolate(
    frame,
    [OUTCOME_START, OUTCOME_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );
  const outcomeScale = interpolate(
    frame,
    [OUTCOME_START, OUTCOME_END],
    [0.7, 1.0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.back(1.7)) }
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
        backdropFilter: "blur(8px)",
        transform: `translateX(${translateX}px)`,
        opacity: panelOpacity,
        overflow: "hidden",
      }}
    >
      {/* Background icon silhouette */}
      <div
        style={{
          position: "absolute",
          top: 140,
          left: "50%",
          transform: "translateX(-50%)",
        }}
      >
        {isLeft ? (
          <NeedleIcon color={accentColor} size={ICON_SIZE} opacity={iconOpacity} />
        ) : (
          <MoldIcon color={accentColor} size={ICON_SIZE} opacity={iconOpacity} />
        )}
      </div>

      {/* Header */}
      <div
        style={{
          position: "absolute",
          top: 260,
          width: "100%",
          textAlign: "center",
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

      {/* Icon (visible, fades with header) */}
      <div
        style={{
          position: "absolute",
          top: 300,
          left: "50%",
          transform: "translateX(-50%)",
          opacity: headerOpacity,
        }}
      >
        {isLeft ? (
          <NeedleIcon color={accentColor} size={60} opacity={0.6} />
        ) : (
          <MoldIcon color={accentColor} size={60} opacity={0.6} />
        )}
      </div>

      {/* Cost curve */}
      <CostCurve
        type={curveType}
        color={accentColor}
        drawStart={curveStart}
        drawEnd={curveEnd}
      />

      {/* Outcome word */}
      <div
        style={{
          position: "absolute",
          top: 660,
          width: "100%",
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontWeight: 900,
          fontSize: OUTCOME_FONT_SIZE,
          color: accentColor,
          textTransform: "uppercase" as const,
          opacity: outcomeOpacity,
          transform: `scale(${outcomeScale})`,
        }}
      >
        {outcomeText}
      </div>
    </div>
  );
};

export default SplitPanel;
